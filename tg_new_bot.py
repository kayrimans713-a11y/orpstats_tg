"""
Telegram-бот мониторинга SA-MP сервера ONLINE RP HAWAII — v10.0 (TG edition).

Порт VK-бота v9.2 на aiogram 3.x.
Все секреты (BOT_TOKEN, OWNER_ID, куки форума) — только из .env / переменных окружения.
В коде хардкодов токенов нет — можно безопасно публиковать на GitHub.

Установка:
    pip install aiogram==3.13.1 matplotlib==3.9.2 python-dotenv==1.0.1

Создай .env рядом с bot.py:
    BOT_TOKEN=...
    OWNER_ID=...
    (остальное опционально, см. .env.example в README)

Запуск:
    python bot.py
"""

import asyncio
import html as html_mod
import json
import logging
import os
import re
import secrets
import socket
import sqlite3
import ssl
import struct
import threading
import time
import urllib.request
import xml.etree.ElementTree as ET
from datetime import datetime, timedelta, timezone
from typing import Optional

from aiogram import Bot, Dispatcher, F, Router
from aiogram.client.default import DefaultBotProperties
from aiogram.enums import ParseMode
from aiogram.filters import Command, CommandStart
from aiogram.types import (
    CallbackQuery,
    FSInputFile,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    KeyboardButton,
    Message,
    ReplyKeyboardMarkup,
    ReplyKeyboardRemove,
)
from dotenv import load_dotenv

try:
    import matplotlib
    matplotlib.use("Agg")
    import matplotlib.dates as mdates
    import matplotlib.pyplot as plt
    HAVE_MPL = True
except Exception:
    HAVE_MPL = False


# ═══════════════════════ КОНФИГ ═══════════════════════
load_dotenv()

BOT_TOKEN   = os.getenv("BOT_TOKEN", "")
OWNER_ID    = int(os.getenv("OWNER_ID", "0"))

SERVER_NAME = os.getenv("SERVER_NAME", "ONLINE RP HAWAII")
SERVER_HOST = os.getenv("SERVER_HOST", "s4.gta-mobile.ru")
SERVER_IP   = os.getenv("SERVER_IP", "95.213.255.224")
SERVER_PORT = int(os.getenv("SERVER_PORT", "7777"))

DB_PATH     = os.getenv("DB_PATH", "hawaii_bot.db")

POLL_INTERVAL    = 5
QUERY_TIMEOUT    = 10
FAILS_TO_OFFLINE = 3
TZ               = timezone(timedelta(hours=3))
DAY_START_HOUR   = 5

MAX_TRACKS      = 20
CHAT_MAX_TRACKS = 10
REARM_GAP       = 3
STATS_HOURS     = 48
CHART_CACHE_SEC = 180
CHART_PATH      = "online_chart.png"
AUTO_INTERVAL   = 30 * 60
PROFILE_DAYS    = 7

FORUM_COOKIES = os.getenv("FORUM_COOKIES", "")
FORUM_RSS     = os.getenv("FORUM_RSS", "https://forum.onlinerp.com/forums/-/index.rss")

# ⚠️ Kristina_Hortis удалена по просьбе заказчика
ADMINS = """
Nathan_Morris Veronika_Lavanda Anna_Orlova Laurent_Sykes Steven_Macalister
Rocky_Rockstar Shay_Cormac Itan_Yonkers Weka_Hewarc Chara_Dreemurr
Egor_Talavera Clayton_Corleone Pavel_Nakozin Cameron_Flores
Kyle_Carlyle Homelander_Quattroki Sasha_Ilumetrezzix
Pioneer_Squirtezzer Sebastian_Nekrasov Charles_Henderson Matthew_Sykes Billy_Russo Hawaii_Bot
Villian_Romanov Negan_Smiths Jason_Watson Matthew_Grassi
Joxa_Aldanyazovv Makar_West Noah_Krasin
""".split()
ADMINS_LOWER = {a.lower(): a for a in ADMINS}

SPECIAL_ADMINS = {
    "sebastian_nekrasov", "charles_henderson", "nathan_morris",
    "veronika_lavanda", "anna_orlova", "laurent_sykes", "steven_macalister",
}

logging.basicConfig(
    level=os.getenv("LOG_LEVEL", "INFO"),
    format="%(asctime)s %(levelname)s %(name)s: %(message)s",
)
log = logging.getLogger("hawaii-bot")
START_TS = time.time()
NICK_RE = re.compile(r"^[A-Za-z0-9_\[\]\(\)\$@\.=]{2,24}$")
EVENT_LABELS = {"mod": "📝 Обновление мода", "down": "🔴 Падение сервера", "up": "🟢 Восстановление"}
CHAT_EVENTS = ("down", "up", "mod")


# ═══════════════════════ SA-MP QUERY ═══════════════════════
def _packet(opcode: bytes) -> bytes:
    return (b"SAMP" + bytes(int(x) for x in SERVER_IP.split("."))
            + struct.pack("<H", SERVER_PORT) + opcode)


def _ask(sock: socket.socket, opcode: bytes) -> bytes:
    pkt = _packet(opcode)
    for _ in range(3):
        sock.sendto(pkt, (SERVER_IP, SERVER_PORT))
        try:
            while True:
                data, _addr = sock.recvfrom(8192)
                if data[:4] == b"SAMP" and data[10:11] == opcode:
                    return data
        except socket.timeout:
            continue
    raise TimeoutError("no response")


def query_server():
    sock = socket.socket(socket.AF_INET, socket.SOCK_DGRAM)
    sock.settimeout(QUERY_TIMEOUT)
    try:
        d = _ask(sock, b"i")
        online, maxp = struct.unpack_from("<HH", d, 12)
        info = {"online": online, "max": maxp, "passworded": bool(d[11]),
                "hostname": "", "gamemode": "", "language": "", "rules": {}}
        try:
            off, strs = 16, []
            for _ in range(3):
                (ln,) = struct.unpack_from("<I", d, off)
                strs.append(d[off + 4: off + 4 + ln].decode("cp1251", "replace"))
                off += 4 + ln
            info["hostname"], info["gamemode"], info["language"] = strs
        except (struct.error, IndexError):
            pass
        try:
            r = _ask(sock, b"r")
            (rc,) = struct.unpack_from("<H", r, 11)
            off = 13
            for _ in range(rc):
                nl = r[off]
                rn = r[off + 1: off + 1 + nl].decode("cp1251", "replace")
                off += 1 + nl
                vl = r[off]
                rv = r[off + 1: off + 1 + vl].decode("cp1251", "replace")
                off += 1 + vl
                info["rules"][rn.lower()] = rv
        except (TimeoutError, struct.error, IndexError):
            pass

        players = None
        for _ in range(3):
            try:
                d = _ask(sock, b"d")
                (cnt,) = struct.unpack_from("<H", d, 11)
                off, players = 13, []
                for _ in range(cnt):
                    pid = d[off]
                    nl = d[off + 1]
                    name = d[off + 2: off + 2 + nl].decode("cp1251", "replace")
                    off += 2 + nl
                    score, ping = struct.unpack_from("<iI", d, off)
                    off += 8
                    players.append({"id": pid, "name": name, "score": score, "ping": ping})
                if online > 0 and not players:
                    players = None
                else:
                    break
            except (TimeoutError, struct.error, IndexError):
                players = None
                time.sleep(1)
        return info, players
    finally:
        sock.close()


# ═══════════════════════ FORUM ═══════════════════════
def check_forum_sync(bot: Bot, loop: asyncio.AbstractEventLoop):
    if not FORUM_COOKIES:
        return
    ctx = ssl.create_default_context()
    ctx.check_hostname = False
    ctx.verify_mode = ssl.CERT_NONE

    req = urllib.request.Request(FORUM_RSS, headers={
        "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
        "Cookie": FORUM_COOKIES,
    })
    try:
        with urllib.request.urlopen(req, context=ctx, timeout=15) as resp:
            root = ET.fromstring(resp.read())
    except Exception as e:
        log.warning("Ошибка парсинга форума: %s", e)
        return

    for item in root.findall(".//item"):
        title_el = item.find("title")
        link_el  = item.find("link")
        date_el  = item.find("pubDate")
        cat_el   = item.find("category")
        if not (title_el is not None and link_el is not None):
            continue
        title = title_el.text or ""
        link  = link_el.text or ""
        pub_date_str = (date_el.text if date_el is not None else "") or ""
        category = (cat_el.text if cat_el is not None else "Раздел неизвестен")

        m = re.search(r"threads/(\d+)/", link)
        if not m:
            continue
        thread_id = int(m.group(1))

        if db_one("SELECT 1 FROM forum_seen WHERE thread_id=?", (thread_id,)):
            continue
        db_exec("INSERT OR IGNORE INTO forum_seen VALUES(?,?)", (thread_id, now()))

        try:
            dt_gmt = datetime.strptime(pub_date_str, "%a, %d %b %Y %H:%M:%S %z")
            time_str = dt_gmt.astimezone(TZ).strftime("%d.%m.%Y %H:%M:%S (МСК)")
        except Exception:
            time_str = pub_date_str

        content_text = "Текст жалобы не удалось загрузить (защита форума)."
        try:
            req_page = urllib.request.Request(link, headers={
                "User-Agent": "Mozilla/5.0 (Windows NT 10.0; Win64; x64)",
                "Cookie": FORUM_COOKIES,
            })
            with urllib.request.urlopen(req_page, context=ctx, timeout=10) as page_resp:
                html_data = page_resp.read().decode("utf-8", errors="ignore")
                m_desc = re.search(r'<meta name="description" content="([^"]+)"', html_data)
                if m_desc:
                    content_text = html_mod.unescape(m_desc.group(1)).strip()
        except Exception:
            pass

        for uid, nick, _enabled in db_all(
            "SELECT user_id, nick, enabled FROM forum_nicks WHERE enabled=1"
        ):
            if nick.lower() in title.lower():
                text = (
                    f"⚖️ На <b>{html_mod.escape(nick)}</b> поступила новая жалоба/обращение\n"
                    f"📌 Заголовок: {html_mod.escape(title)}\n"
                    f"📂 Раздел: {html_mod.escape(category)}\n"
                    f"🕒 Время: {time_str}\n"
                    f"📝 Содержание:\n{html_mod.escape(content_text)}\n\n"
                    f"🔗 <a href=\"{link}\">Ссылка</a>"
                )
                asyncio.run_coroutine_threadsafe(safe_send(bot, uid, text), loop)


# ═══════════════════════ БАЗА ═══════════════════════
_db = sqlite3.connect(DB_PATH, check_same_thread=False)
_lock = threading.Lock()
_db.executescript("""
CREATE TABLE IF NOT EXISTS users(user_id INTEGER PRIMARY KEY, first_seen INTEGER, last_seen INTEGER, requests INTEGER DEFAULT 0, nick TEXT);
CREATE TABLE IF NOT EXISTS allowed_users(user_id INTEGER PRIMARY KEY, added_by INTEGER, added_at INTEGER);
CREATE TABLE IF NOT EXISTS blocked(user_id INTEGER PRIMARY KEY, blocked_at INTEGER);
CREATE TABLE IF NOT EXISTS players(
    name_lower TEXT PRIMARY KEY, name TEXT, online INTEGER DEFAULT 0,
    last_join INTEGER, last_leave INTEGER, last_seen INTEGER, score INTEGER);
CREATE TABLE IF NOT EXISTS history(ts INTEGER, online INTEGER, admins INTEGER);
CREATE INDEX IF NOT EXISTS idx_hist ON history(ts);
CREATE TABLE IF NOT EXISTS tracks(
    user_id INTEGER, name_lower TEXT, name TEXT, added_at INTEGER,
    PRIMARY KEY(user_id, name_lower));
CREATE TABLE IF NOT EXISTS online_tracks(
    user_id INTEGER, threshold INTEGER, armed INTEGER DEFAULT 1,
    PRIMARY KEY(user_id, threshold));
CREATE TABLE IF NOT EXISTS event_tracks(user_id INTEGER, kind TEXT, PRIMARY KEY(user_id, kind));
CREATE TABLE IF NOT EXISTS sessions(name_lower TEXT, join_ts INTEGER, leave_ts INTEGER);
CREATE INDEX IF NOT EXISTS idx_sess ON sessions(name_lower, join_ts);
CREATE TABLE IF NOT EXISTS bot_admins(user_id INTEGER PRIMARY KEY, added_by INTEGER, added_at INTEGER);
CREATE TABLE IF NOT EXISTS auto_notify(user_id INTEGER PRIMARY KEY, last_sent INTEGER);
CREATE TABLE IF NOT EXISTS kv(k TEXT PRIMARY KEY, v TEXT);
CREATE TABLE IF NOT EXISTS chat_admins(chat_id INTEGER PRIMARY KEY, user_id INTEGER, added_at INTEGER);
CREATE TABLE IF NOT EXISTS chat_settings(
    chat_id INTEGER PRIMARY KEY, tracks INTEGER DEFAULT 1,
    down INTEGER DEFAULT 1, up INTEGER DEFAULT 1, nickchanges INTEGER DEFAULT 0,
    allow_cmds INTEGER DEFAULT 1, title TEXT);
CREATE TABLE IF NOT EXISTS chat_tracks(
    chat_id INTEGER, kind TEXT, value TEXT, added_by INTEGER, added_at INTEGER,
    PRIMARY KEY(chat_id, kind, value));
CREATE TABLE IF NOT EXISTS admin_ranks(name_lower TEXT PRIMARY KEY, rank TEXT);
CREATE TABLE IF NOT EXISTS nick_watchers(user_id INTEGER PRIMARY KEY);
CREATE TABLE IF NOT EXISTS nick_changes_log(
    id INTEGER PRIMARY KEY AUTOINCREMENT, ts INTEGER, player_id INTEGER,
    old_nick TEXT, new_nick TEXT);
CREATE TABLE IF NOT EXISTS registrations(ts INTEGER, player_id INTEGER, nick TEXT);
CREATE TABLE IF NOT EXISTS greet_watchers(
    user_id INTEGER PRIMARY KEY, morning INTEGER DEFAULT 1,
    night INTEGER DEFAULT 1, night_replied INTEGER DEFAULT 0);
CREATE TABLE IF NOT EXISTS forum_nicks(user_id INTEGER PRIMARY KEY, nick TEXT, enabled INTEGER DEFAULT 1);
CREATE TABLE IF NOT EXISTS forum_seen(thread_id INTEGER PRIMARY KEY, ts INTEGER);
""")
_db.commit()


def db_exec(sql, args=()):
    with _lock:
        cur = _db.execute(sql, args)
        _db.commit()
        return cur.rowcount


def db_one(sql, args=()):
    with _lock:
        return _db.execute(sql, args).fetchone()


def db_all(sql, args=()):
    with _lock:
        return _db.execute(sql, args).fetchall()


def kv_get(k):
    r = db_one("SELECT v FROM kv WHERE k=?", (k,))
    return r[0] if r else None


def kv_set(k, v):
    db_exec("INSERT INTO kv VALUES(?,?) ON CONFLICT(k) DO UPDATE SET v=?", (k, str(v), str(v)))


state = {"up": None, "info": None, "players": None, "last_ok": None, "fails": 0, "since": None}


def now() -> int:
    return int(time.time())


def fmt_dt(ts) -> str:
    return datetime.fromtimestamp(ts, TZ).strftime("%d.%m.%Y %H:%M:%S")


def fmt_hm(ts) -> str:
    return datetime.fromtimestamp(ts, TZ).strftime("%H:%M")


def fmt_dur(sec) -> str:
    sec = max(0, int(sec))
    d, r = divmod(sec, 86400)
    h, r = divmod(r, 3600)
    m, s = divmod(r, 60)
    parts = []
    if d: parts.append(f"{d} д")
    if h: parts.append(f"{h} ч")
    if m: parts.append(f"{m} мин")
    if not parts: parts.append(f"{s} сек")
    return " ".join(parts[:2])


def ago(ts) -> str:
    d = now() - ts
    return "только что" if d < 30 else f"{fmt_dur(d)} назад"


def day_start_ts(t=None) -> int:
    dt = datetime.fromtimestamp(t or now(), TZ)
    start = dt.replace(hour=DAY_START_HOUR, minute=0, second=0, microsecond=0)
    if dt < start:
        start -= timedelta(days=1)
    return int(start.timestamp())


if kv_get("monitor_since") is None:
    first = db_one("SELECT MIN(ts) FROM history")
    kv_set("monitor_since", (first[0] if first and first[0] else now()))


def is_maintenance() -> bool:
    end = int(kv_get("maint_end") or 0)
    if end == 0:
        return False
    if now() > end:
        kv_set("maint_end", 0)
        return False
    return True


def get_maint_text() -> str:
    end = int(kv_get("maint_end") or 0)
    if end == 0:
        return ""
    left = end - now()
    if left > 0:
        return f"🟠 Бот на тех.обслуживании, подождите {fmt_dur(left)}."
    return "🟠 Бот на тех.обслуживании, скоро заработает."


# ═══════════════════════ РОЛИ ═══════════════════════
def is_owner(uid: int) -> bool:
    return OWNER_ID != 0 and uid == OWNER_ID


def is_staff(uid: int) -> bool:
    return is_owner(uid) or bool(db_one("SELECT 1 FROM bot_admins WHERE user_id=?", (uid,)))


def has_access(uid: int) -> bool:
    if is_owner(uid) or is_staff(uid):
        return True
    return bool(db_one("SELECT 1 FROM allowed_users WHERE user_id=?", (uid,)))


def chat_admin_of(chat_id: int):
    r = db_one("SELECT user_id FROM chat_admins WHERE chat_id=?", (chat_id,))
    return r[0] if r else None


def is_chat_admin(uid: int, chat_id: int) -> bool:
    if is_owner(uid):
        return True
    return chat_admin_of(chat_id) == uid


def chat_ensure(chat_id: int, title: Optional[str] = None):
    if chat_id >= 0:
        return
    db_exec("INSERT OR IGNORE INTO chat_settings(chat_id) VALUES(?)", (chat_id,))
    if title:
        db_exec("UPDATE chat_settings SET title=? WHERE chat_id=?", (title[:60], chat_id))


def chat_cfg(chat_id: int) -> dict:
    r = db_one("SELECT tracks, down, up, nickchanges, allow_cmds FROM chat_settings WHERE chat_id=?", (chat_id,))
    if not r:
        return {"tracks": 1, "down": 1, "up": 1, "nickchanges": 0, "allow_cmds": 1}
    return {"tracks": r[0], "down": r[1], "up": r[2], "nickchanges": r[3], "allow_cmds": r[4]}


def chat_cfg_set(chat_id: int, key: str, val: int):
    db_exec(f"UPDATE chat_settings SET {key}=? WHERE chat_id=?", (val, chat_id))


def all_chat_ids() -> list:
    return [r[0] for r in db_all("SELECT chat_id FROM chat_settings")]


def rank_of(name: str) -> str:
    r = db_one("SELECT rank FROM admin_ranks WHERE name_lower=?", (name.lower(),))
    return r[0] if r else ""


# ═══════════════════════ BOT INIT ═══════════════════════
if not BOT_TOKEN:
    raise SystemExit("Не задан BOT_TOKEN в .env")

bot = Bot(token=BOT_TOKEN, default=DefaultBotProperties(parse_mode=ParseMode.HTML))
dp  = Dispatcher()
router = Router()
dp.include_router(router)

_loop: Optional[asyncio.AbstractEventLoop] = None


# ═══════════════════════ SEND HELPERS ═══════════════════════
async def safe_send(chat_id: int, text: str, **kwargs):
    if is_maintenance() and not is_owner(chat_id):
        await bot.send_message(chat_id, get_maint_text())
        return
    try:
        await bot.send_message(chat_id, text[:4000], disable_web_page_preview=True, **kwargs)
    except Exception as e:
        log.warning("Не доставлено %s: %s", chat_id, e)


async def notify(uid: int, text: str):
    if is_maintenance():
        return
    await safe_send(uid, text)
    await asyncio.sleep(0.05)


async def notify_event(kind: str, text: str):
    if is_maintenance():
        return
    for (uid,) in db_all("SELECT user_id FROM event_tracks WHERE kind=?", (kind,)):
        await notify(uid, text)
    for chat_id in all_chat_ids():
        cfg = chat_cfg(chat_id)
        if not cfg.get("tracks"):
            continue
        if kind in ("down", "up") and not cfg.get(kind):
            continue
        if not db_one("SELECT 1 FROM chat_tracks WHERE chat_id=? AND kind=?", (chat_id, kind)):
            continue
        await safe_send(chat_id, text)


async def send_long(chat_id: int, text: str):
    chunk, size = [], 0
    for line in text.split("\n"):
        if size + len(line) + 1 > 3500 and chunk:
            await safe_send(chat_id, "\n".join(chunk))
            chunk, size = [], 0
        chunk.append(line)
        size += len(line) + 1
    if chunk:
        await safe_send(chat_id, "\n".join(chunk))


# ═══════════════════════ МОНИТОРИНГ ═══════════════════════
def apply_players(players):
    t = now()
    current = {p["name"].lower(): p for p in players}
    joined, left = [], []

    current_ids = {str(p["id"]): p["name"] for p in players}
    last_online_json = kv_get("last_online_players")
    last_online = {}
    if last_online_json:
        try:
            last_online = json.loads(last_online_json)
        except Exception:
            pass

    changes = []
    for pid_str, new_name in current_ids.items():
        if pid_str in last_online:
            old_name = last_online[pid_str]
            if old_name.lower() != new_name.lower():
                if old_name.lower().startswith("orpuserunauthorized_") or \
                   new_name.lower().startswith("orpuserunauthorized_"):
                    continue
                row = db_one("SELECT last_leave, last_join FROM players WHERE name_lower=?", (old_name.lower(),))
                if row and row[1] and row[1] >= t - 120:
                    changes.append((int(pid_str), old_name, new_name))

    with _lock:
        cur = _db.cursor()
        was = {r[0]: (r[1], r[2]) for r in cur.execute(
            "SELECT name_lower, name, last_join FROM players WHERE online=1")}

        for low, p in current.items():
            if low in was:
                cur.execute("UPDATE players SET last_seen=?, name=?, score=? WHERE name_lower=?",
                            (t, p["name"], p["score"], low))
            else:
                if not p["name"].lower().startswith("orpuserunauthorized_"):
                    joined.append(p["name"])
                cur.execute(
                    "INSERT INTO players(name_lower,name,online,last_join,last_seen,score) VALUES(?,?,1,?,?,?) "
                    "ON CONFLICT(name_lower) DO UPDATE SET online=1,last_join=?,last_seen=?,name=?,score=?",
                    (low, p["name"], t, t, p["score"], t, t, p["name"], p["score"]))
                cur.execute("INSERT INTO sessions VALUES(?,?,NULL)", (low, t))

        for low, (name, last_join) in was.items():
            if low not in current:
                if not name.lower().startswith("orpuserunauthorized_"):
                    left.append((name, last_join, t))
                cur.execute("UPDATE players SET online=0, last_leave=? WHERE name_lower=?", (t, low))
                cur.execute("UPDATE sessions SET leave_ts=? WHERE name_lower=? AND leave_ts IS NULL", (t, low))
        _db.commit()

    if is_maintenance():
        kv_set("last_online_players", json.dumps(current_ids))
        return [], []

    for pid, old_n, new_n in changes:
        if old_n.lower().startswith("orpuserunauthorized_"):
            reg_check = db_one("SELECT 1 FROM registrations WHERE player_id=? OR nick=?", (pid, new_n))
            if not reg_check:
                db_exec("INSERT INTO registrations (ts, player_id, nick) VALUES(?,?,?)", (t, pid, new_n))
        else:
            db_exec("INSERT INTO nick_changes_log (ts, player_id, old_nick, new_nick) VALUES(?,?,?,?)",
                    (t, pid, old_n, new_n))
            text = (f"#changes\n🔄 Смена никнейма:\nID: {pid}\n"
                    f"Старый: {html_mod.escape(old_n)}\n"
                    f"Новый: {html_mod.escape(new_n)}\n"
                    f"Время: {fmt_dt(t)} (МСК)")
            for (uid,) in db_all("SELECT user_id FROM nick_watchers"):
                asyncio.run_coroutine_threadsafe(notify(uid, text), _loop)
            for chat_id in all_chat_ids():
                if chat_cfg(chat_id).get("nickchanges"):
                    asyncio.run_coroutine_threadsafe(safe_send(chat_id, text), _loop)

    kv_set("last_online_players", json.dumps(current_ids))
    return joined, left


async def notify_players(joined, left, online):
    if is_maintenance():
        return
    t = now()
    for name in joined:
        is_special = name.lower() in SPECIAL_ADMINS
        for (uid,) in db_all("SELECT user_id FROM tracks WHERE name_lower=?", (name.lower(),)):
            if is_special and not is_staff(uid):
                continue
            await notify(uid, f"🟢 <b>{html_mod.escape(name)}</b> зашёл на сервер\n"
                              f"Время: {fmt_dt(t)} (МСК)\nОнлайн сервера: {online}")
        for chat_id in all_chat_ids():
            if chat_cfg(chat_id).get("tracks") and db_one(
                    "SELECT 1 FROM chat_tracks WHERE chat_id=? AND kind='player' AND value=?",
                    (chat_id, name.lower())):
                if is_special:
                    continue
                await safe_send(chat_id, f"🟢 <b>{html_mod.escape(name)}</b> зашёл на сервер\n"
                                         f"Время: {fmt_dt(t)} (МСК)\nОнлайн сервера: {online}")

    for name, last_join, lt in left:
        is_special = name.lower() in SPECIAL_ADMINS
        dur = f"\nБыл в сети: {fmt_dur(lt - last_join)}" if last_join else ""
        for (uid,) in db_all("SELECT user_id FROM tracks WHERE name_lower=?", (name.lower(),)):
            if is_special and not is_staff(uid):
                continue
            await notify(uid, f"⚫ <b>{html_mod.escape(name)}</b> вышел с сервера\n"
                              f"Время: {fmt_dt(lt)} (МСК){dur}\nОнлайн сервера: {online}")
        for chat_id in all_chat_ids():
            if chat_cfg(chat_id).get("tracks") and db_one(
                    "SELECT 1 FROM chat_tracks WHERE chat_id=? AND kind='player' AND value=?",
                    (chat_id, name.lower())):
                if is_special:
                    continue
                await safe_send(chat_id, f"⚫ <b>{html_mod.escape(name)}</b> вышел с сервера\n"
                                         f"Время: {fmt_dt(lt)} (МСК){dur}\nОнлайн сервера: {online}")


async def check_online_thresholds(online):
    if is_maintenance():
        return
    for uid, th, armed in db_all("SELECT user_id, threshold, armed FROM online_tracks"):
        if armed and online >= th:
            db_exec("UPDATE online_tracks SET armed=0 WHERE user_id=? AND threshold=?", (uid, th))
            await notify(uid, f"📈 Онлайн сервера достиг {th}!\nСейчас в сети: {online}")
        elif not armed and online <= max(0, th - REARM_GAP):
            db_exec("UPDATE online_tracks SET armed=1 WHERE user_id=? AND threshold=?", (uid, th))

    for chat_id, th in db_all("SELECT chat_id, value FROM chat_tracks WHERE kind='online'"):
        try:
            th = int(th)
        except ValueError:
            continue
        key = f"chat_armed_{chat_id}_{th}"
        a = kv_get(key)
        a = int(a) if a is not None else 1
        if a and online >= th:
            kv_set(key, 0)
            if chat_cfg(chat_id).get("tracks"):
                await safe_send(chat_id, f"📈 Онлайн сервера достиг {th}!\nСейчас в сети: {online}")
        elif not a and online <= max(0, th - REARM_GAP):
            kv_set(key, 1)

    for chat_id, th in db_all("SELECT chat_id, value FROM chat_tracks WHERE kind='online_fall'"):
        try:
            th = int(th)
        except ValueError:
            continue
        key = f"chat_armed_fall_{chat_id}_{th}"
        a = kv_get(key)
        a = int(a) if a is not None else 1
        if a and online <= th:
            kv_set(key, 0)
            if chat_cfg(chat_id).get("tracks"):
                await safe_send(chat_id, f"📉 Онлайн сервера упал до {th}!\nСейчас в сети: {online}")
        elif not a and online >= th + REARM_GAP:
            kv_set(key, 1)


async def check_mod_change(info):
    if is_maintenance():
        return
    sig = f"{info.get('gamemode', '')} | {info.get('rules', {}).get('version', '')}"
    if sig.strip(" |") == "":
        return
    old = kv_get("mod_sig")
    if old != sig:
        kv_set("mod_sig", sig)
        if old is not None:
            await notify_event("mod", f"📝 Обновление мода на сервере\nБыло: {html_mod.escape(old)}\nСтало: {html_mod.escape(sig)}")


async def monitor_loop():
    global _loop
    prune_at = 0
    last_forum_check = 0
    while True:
        try:
            if now() - last_forum_check > 300:
                last_forum_check = now()
                threading.Thread(target=check_forum_sync, args=(bot, _loop), daemon=True).start()

            info, players = await asyncio.to_thread(query_server)
        except Exception as e:
            state["fails"] += 1
            log.warning("Опрос не удался (%s): %s", state["fails"], e)
            if state["fails"] >= FAILS_TO_OFFLINE and state["up"] is not False:
                was_up = state["up"] is True
                state.update(up=False, players=None, since=now())
                if was_up:
                    try:
                        await notify_event("down", f"🔴 Сервер {SERVER_NAME} недоступен\n"
                                                   f"Время: {fmt_dt(now())} (МСК)")
                    except Exception:
                        log.exception("Ошибка уведомления о падении")
            await asyncio.sleep(POLL_INTERVAL)
            continue

        try:
            was_down = state["up"] is False
            first_ok = state["last_ok"] is None
            can_notify = state["up"] is True and state["players"] is not None
            down_since = state["since"]
            if not state["up"]:
                state["since"] = now()

            if players is None:
                state.update(up=True, info=info, last_ok=now(), fails=0)
                adm = sum(1 for p in (players or []) if p["name"].lower() in ADMINS_LOWER)
                db_exec("INSERT INTO history VALUES(?,?,?)", (now(), info["online"], adm))
                await check_online_thresholds(info["online"])
                await check_mod_change(info)
                await asyncio.sleep(POLL_INTERVAL)
                continue

            state.update(up=True, info=info, players=players, last_ok=now(), fails=0)

            if was_down and down_since:
                await notify_event("up",
                    f"🟢 Сервер {SERVER_NAME} снова доступен\n"
                    f"Был недоступен: {fmt_dur(now() - down_since)}\n"
                    f"Онлайн: {info['online']}")

            joined, left = apply_players(players)
            if can_notify and not first_ok:
                await notify_players(joined, left, info["online"])

            adm = sum(1 for p in (players or []) if p["name"].lower() in ADMINS_LOWER)
            db_exec("INSERT INTO history VALUES(?,?,?)", (now(), info["online"], adm))
            await check_online_thresholds(info["online"])
            await check_mod_change(info)
            if now() - prune_at > 3600:
                prune_at = now()
                db_exec("DELETE FROM history WHERE ts < ?", (now() - 3 * 86400,))
                db_exec("DELETE FROM sessions WHERE leave_ts IS NOT NULL AND leave_ts < ?", (now() - 30 * 86400,))
        except Exception:
            log.exception("Ошибка в цикле мониторинга")
        await asyncio.sleep(POLL_INTERVAL)


# ═══════════════════════ ГРАФИК ═══════════════════════
_chart = {"ts": 0, "path": None}
_chart_lock = threading.Lock()


def build_chart_sync() -> Optional[str]:
    if not HAVE_MPL:
        return None
    with _chart_lock:
        if _chart["path"] and now() - _chart["ts"] < CHART_CACHE_SEC:
            return _chart["path"]
        try:
            rows = db_all("SELECT ts, online FROM history WHERE ts >= ? ORDER BY ts",
                          (now() - STATS_HOURS * 3600,))
            if len(rows) < 3:
                return None
            xs = [datetime.fromtimestamp(t, TZ) for t, _ in rows]
            ys = [o for _, o in rows]
            bg = "#1b2330"
            fig, ax = plt.subplots(figsize=(9, 3.4), dpi=110)
            fig.patch.set_facecolor(bg)
            ax.set_facecolor(bg)
            ax.plot(xs, ys, color="#4f8fe8", linewidth=1.4)
            ax.fill_between(xs, ys, color="#4f8fe8", alpha=0.15)
            ax.set_ylim(bottom=0)
            ax.xaxis.set_major_locator(mdates.HourLocator(byhour=[0, 6, 12, 18], tz=TZ))
            ax.xaxis.set_major_formatter(mdates.DateFormatter("%H:%M", tz=TZ))
            ax.tick_params(colors="#9aa7b8", labelsize=8)
            for s in ax.spines.values():
                s.set_visible(False)
            ax.grid(color="#2c3849", linewidth=0.6)
            ax.set_title(f"Онлайн за {STATS_HOURS} ч (МСК)", color="#d7e0ec", fontsize=10)
            fig.tight_layout()
            fig.savefig(CHART_PATH, facecolor=bg)
            plt.close(fig)
            _chart.update(ts=now(), path=CHART_PATH)
            return CHART_PATH
        except Exception as e:
            log.warning("График не создан: %s", e)
            return None


# ═══════════════════════ ТРЕКЕРЫ (ЛИЧКА) ═══════════════════════
def tracker_count(uid: int) -> int:
    return sum(
        (db_one(f"SELECT COUNT(*) FROM {t} WHERE user_id=?", (uid,)) or [0])[0]
        for t in ("tracks", "online_tracks", "event_tracks")
    )


def is_tracked(uid: int, name: str) -> bool:
    return bool(db_one("SELECT 1 FROM tracks WHERE user_id=? AND name_lower=?", (uid, name.lower())))


def cmd_track(uid: int, arg: str) -> str:
    nick = arg.strip().replace(" ", "_")
    if not NICK_RE.match(nick):
        return "Укажи ник игрока, например: /track Laurent_Sykes"
    row = db_one("SELECT name, online FROM players WHERE name_lower=?", (nick.lower(),))
    name = row[0] if row else nick
    if is_tracked(uid, name):
        return f"Ты уже следишь за {name}."
    if tracker_count(uid) >= MAX_TRACKS:
        return f"Лимит трекеров — {MAX_TRACKS}. Убери ненужные: /tracklist."
    db_exec("INSERT OR IGNORE INTO tracks VALUES(?,?,?,?)", (uid, name.lower(), name, now()))
    status = "\nСейчас: 🟢 в сети" if row and row[1] else ("\nСейчас: ⚫ не в сети" if row else "")
    return f"🔔 Слежу за <b>{html_mod.escape(name)}</b>. Напишу, когда он зайдёт или выйдет.{status}"


def cmd_untrack(uid: int, arg: str) -> str:
    nick = arg.strip().replace(" ", "_").lower()
    if not nick:
        return "Использование: /untrack ник"
    n = db_exec("DELETE FROM tracks WHERE user_id=? AND name_lower=?", (uid, nick))
    return f"🔕 Больше не слежу за {html_mod.escape(arg.strip())}." if n else "Ты не следил за этим игроком."


def add_online_track(uid: int, th: int) -> str:
    if db_one("SELECT 1 FROM online_tracks WHERE user_id=? AND threshold=?", (uid, th)):
        return f"Порог {th} уже стоит."
    if tracker_count(uid) >= MAX_TRACKS:
        return f"Лимит трекеров — {MAX_TRACKS}. Убери ненужные: /tracklist."
    cur_online = (state["info"] or {}).get("online") if state["up"] else None
    armed = 0 if (cur_online is not None and cur_online >= th) else 1
    db_exec("INSERT INTO online_tracks VALUES(?,?,?)", (uid, th, armed))
    msg = f"🔔 Напишу, когда онлайн сервера достигнет {th}."
    if not armed:
        msg += (f"\nСейчас онлайн уже {cur_online}, поэтому уведомление придёт, "
                f"когда он упадёт до {max(0, th - REARM_GAP)} и снова поднимется до {th}.")
    return msg


def cmd_trackonline(uid: int, arg: str) -> str:
    if not arg.strip().isdigit() or not (1 <= int(arg) <= 1000):
        return "Укажи число от 1 до 1000, например: /trackonline 50"
    return add_online_track(uid, int(arg))


def cmd_untrackonline(uid: int, arg: str) -> str:
    if not arg.strip().isdigit():
        return "Использование: /untrackonline число"
    n = db_exec("DELETE FROM online_tracks WHERE user_id=? AND threshold=?", (uid, int(arg)))
    return f"🔕 Порог {int(arg)} убран." if n else "Такого порога у тебя нет."


def toggle_tracker(uid: int, pl: dict) -> str:
    kind = pl.get("k")
    if kind == "online":
        th = int(pl.get("n", 0))
        if db_one("SELECT 1 FROM online_tracks WHERE user_id=? AND threshold=?", (uid, th)):
            db_exec("DELETE FROM online_tracks WHERE user_id=? AND threshold=?", (uid, th))
            return f"🔕 Порог онлайна {th} выключен."
        return add_online_track(uid, th)
    if kind in EVENT_LABELS:
        if db_one("SELECT 1 FROM event_tracks WHERE user_id=? AND kind=?", (uid, kind)):
            db_exec("DELETE FROM event_tracks WHERE user_id=? AND kind=?", (uid, kind))
            return f"🔕 Выключено: {EVENT_LABELS[kind]}."
        if tracker_count(uid) >= MAX_TRACKS:
            return f"Лимит трекеров — {MAX_TRACKS}. Убери ненужные: /tracklist."
        db_exec("INSERT OR IGNORE INTO event_tracks VALUES(?,?)", (uid, kind))
        return f"🔔 Включено: {EVENT_LABELS[kind]}. Напишу в личку."
    return "Неизвестный трекер."


def cmd_tracklist(uid: int) -> str:
    players = db_all(
        "SELECT t.name, p.online FROM tracks t "
        "LEFT JOIN players p ON p.name_lower = t.name_lower "
        "WHERE t.user_id=? ORDER BY t.name", (uid,))
    ths = db_all("SELECT threshold FROM online_tracks WHERE user_id=? ORDER BY threshold", (uid,))
    evs = db_all("SELECT kind FROM event_tracks WHERE user_id=?", (uid,))
    if not (players or ths or evs):
        return ("🔔 Трекер пуст.\n\n"
                "/track ник — следить за игроком\n"
                "/trackonline число — порог онлайна сервера\n"
                "Или просто пришли ник — покажу карточку с кнопкой «Следить».")
    lines = [f"🔔 Твой трекер ({tracker_count(uid)}/{MAX_TRACKS})\n"]
    if players:
        lines.append("Игроки:")
        lines += [f"{'🟢' if online else '⚫'} {html_mod.escape(name)}" for name, online in players]
    if ths:
        lines.append("\nПороги онлайна: " + ", ".join(str(t[0]) for t in ths))
    if evs:
        lines.append("События: " + ", ".join(EVENT_LABELS.get(k[0], k[0]) for k in evs))
    lines.append("\nУбрать: /untrack ник, /untrackonline число")
    return "\n".join(lines)


# ═══════════════════════ БЕСЕДЫ ═══════════════════════
def chat_track_count(chat_id: int) -> int:
    return (db_one("SELECT COUNT(*) FROM chat_tracks WHERE chat_id=?", (chat_id,)) or [0])[0]


def chat_add_track(chat_id: int, kind: str, value: str, by: int) -> str:
    if chat_track_count(chat_id) >= CHAT_MAX_TRACKS:
        return f"Лимит трекеров беседы — {CHAT_MAX_TRACKS}. Убери ненужные: /tracklist."
    if db_one("SELECT 1 FROM chat_tracks WHERE chat_id=? AND kind=? AND value=?", (chat_id, kind, value)):
        return "Такой трекер уже есть."
    db_exec("INSERT INTO chat_tracks VALUES(?,?,?,?,?)", (chat_id, kind, value, by, now()))
    if kind == "online":
        kv_set(f"chat_armed_{chat_id}_{value}", 1)
    if kind == "online_fall":
        kv_set(f"chat_armed_fall_{chat_id}_{value}", 1)
    if kind == "player":
        row = db_one("SELECT name, online FROM players WHERE name_lower=?", (value.lower(),))
        return f"🔔 Беседа следит за {html_mod.escape(row[0] if row else value)}."
    if kind == "online":
        return f"🔔 Беседа следит за онлайном ≥ {value}."
    if kind == "online_fall":
        return f"🔔 Беседа следит за падением онлайна до {value}."
    return f"🔔 Беседа подписана: {EVENT_LABELS.get(kind, kind)}."


def chat_del_track(chat_id: int, kind: str, value: str) -> str:
    n = db_exec("DELETE FROM chat_tracks WHERE chat_id=? AND kind=? AND value=?", (chat_id, kind, value))
    return "🔕 Трекер убран." if n else "Такого трекера нет."


def cmd_chat_tracklist(chat_id: int) -> str:
    rows = db_all("SELECT kind, value FROM chat_tracks WHERE chat_id=? ORDER BY kind, value", (chat_id,))
    if not rows:
        return (f"🔔 Трекеры беседы пусты.\n"
                f"/track Ник — следить за игроком\n"
                f"/trackonline N — порог онлайна\n"
                f"/trackonlinefall N — падение онлайна до N\n"
                f"/trackevent down|up|mod — событие сервера\n"
                f"Лимит — {CHAT_MAX_TRACKS} на беседу.")
    lines = [f"🔔 Трекеры беседы ({len(rows)}/{CHAT_MAX_TRACKS})\n"]
    for kind, value in rows:
        if kind == "player":
            row = db_one("SELECT online FROM players WHERE name_lower=?", (value,))
            mark = "🟢" if row and row[0] else "⚫"
            lines.append(f"{mark} игрок: {html_mod.escape(value)}")
        elif kind == "online":
            lines.append(f"📈 онлайн ≥ {value}")
        elif kind == "online_fall":
            lines.append(f"📉 онлайн падает до {value}")
        else:
            lines.append(f"{EVENT_LABELS.get(kind, kind)}")
    lines.append("\nУбрать: /untrack Ник, /untrackonline N, /untrackonlinefall N, /untrackevent down|up|mod")
    return "\n".join(lines)


def cmd_chats() -> str:
    rows = db_all("SELECT chat_id, tracks, down, up, nickchanges, allow_cmds, title FROM chat_settings")
    if not rows:
        return "⚙️ Известных бесед нет."
    lines = ["⚙️ Известные беседы:\n"]
    def onoff(v):
        return "вкл" if v else "выкл"
    for chat_id, tr, dn, up, nc, cmds, title in rows:
        adm = chat_admin_of(chat_id)
        adm_s = f"id{adm}" if adm else "не назначен"
        name_s = f" «{title}»" if title else ""
        lines.append(
            f"ID: {chat_id}{name_s}\n"
            f"  админ: {adm_s}\n"
            f"  трекеры: {onoff(tr)} | падение: {onoff(dn)} | восстановление: {onoff(up)} | смены ников: {onoff(nc)} | команды: {onoff(cmds)}\n"
            f"  трекеров: {chat_track_count(chat_id)}/{CHAT_MAX_TRACKS}")
    return "\n".join(lines)


# ═══════════════════════ КОМАНДЫ ═══════════════════════
def cmd_start(uid: int) -> str:
    text = (f"👋 Привет! Я слежу за сервером {SERVER_NAME}.\n\n"
            "🔎 Узнать про игрока: просто отправь мне его ник (например Laurent_Sykes) — покажу, "
            "в сети ли он, когда заходил и выходил, уровень и время в игре.\n\n"
            "📋 Команды:\n"
            "/server — статистика сервера: онлайн, пик, мод, версия, график\n"
            "/players — ники игроков, которые сейчас в игре\n"
            "/stats — статистика бота\n"
            "/profile — моя статистика за 7 игровых дней\n"
            "/setnick Ник — привязать свой игровой ник\n"
            "/pstats Ник — статистика любого игрока за 7 дней\n"
            "/hidekb — скрыть кнопки в личке\n\n"
            "🔔 Трекер (уведомления в личку):\n"
            "/track Ник — уведомить, когда игрок зайдёт или выйдет\n"
            "/untrack Ник — перестать следить\n"
            "/trackonline число — уведомить, когда онлайн сервера достигнет числа\n"
            "/untrackonline число — убрать порог\n"
            "/tracklist — всё, что отслеживаешь\n\n"
            "⚖️ Форум:\n"
            "/setforumnick Ник — следить за жалобами на форуме\n"
            "/forumoff — отключить уведомления о жалобах\n\n"
            f"🕔 Серверные сутки считаются с {DAY_START_HOUR:02d}:00 по МСК.\n"
            "/menu — показать кнопки")
    if is_staff(uid):
        text += ("\n\n👮 Команды администрации бота:\n"
                 "/admins — администрация сервера онлайн\n"
                 "/autoinfo — автоотчёт о сервере каждые 30 минут (вкл/выкл)\n"
                 "/nickchanges on|off — уведы о смене ников игроков\n"
                 "/regstats — сколько человек зарегалось сегодня\n"
                 "/greetings on|off — приветствия (утро/ночь)\n"
                 "/logs — история обновлений бота")
    if is_owner(uid):
        text += ("\n\n👑 Команды основателя:\n"
                 "/allow <id|@username> — выдать доступ к боту\n"
                 "/deny <id|@username> — забрать доступ\n"
                 "/allowlist — список с доступом\n"
                 "/block <id|@username> — заблокировать пользователя\n"
                 "/unblock <id|@username> — разблокировать\n"
                 "/newadm <id|@username> — назначить админа бота\n"
                 "/deladm <id|@username> — снять админа бота\n"
                 "/admlist — список админов бота\n"
                 "/chats — рабочие беседы и их настройки\n"
                 "/setchatadmin <chat_id> <id|@username> — назначить админа беседы\n"
                 "/delchatadmin <chat_id> — снять админа беседы\n"
                 "/setrank Ник Ранг — задать ранг админа сервера\n"
                 "/delrank Ник — убрать ранг\n"
                 "/maintenance <минут> — включить тех.перерыв (0 - выключить)\n"
                 "📣 Рассылка: перешли мне пост или отправь сообщение с картинкой.")
    return text


def cmd_logs() -> str:
    return (
        "📜 История обновлений бота:\n\n"
        "🟢 v10.0 (TG edition)\n"
        "• Порт VK-бота v9.2 на Telegram (aiogram 3.x).\n"
        "• Kristina_Hortis убрана из списка админов.\n"
        "• Секреты только в .env.\n\n"
        "🟢 v9.2\n"
        "• Исправлен формат даты в уведомлениях форума (МСК, русский).\n"
        "• Добавлен парсинг заголовка и первого сообщения из жалобы.\n"
        "• Убран Angel_Gonzalez.\n\n"
        "🟢 v9.1\n"
        "• Добавлен трекер жалоб с форума.\n"
        "• Команды /setforumnick и /forumoff.\n\n"
        "🟢 v8.7\n"
        "• Жёсткая блокировка уведомлений во время тех.обслуживания.\n"
        "• Понятное сообщение, если сервер не отдаёт список игроков.\n\n"
        "🟢 v8.0\n"
        "• Исправлен флуд сменами ников.\n"
        "• Добавлен режим тех.обслуживания.\n\n"
        "🟢 v7.0\n"
        "• Привязка бесед через /peerid (теперь /chatid).\n"
        "• Уведомления о смене ников (#changes) в беседы.\n\n"
        "🟢 v6.8\n"
        "• Уменьшен интервал опроса до 5 секунд для точного отслеживания перезаходов.\n"
    )


def cmd_admins() -> str:
    if state["up"] is None:
        return "⏳ Данные ещё загружаются, попробуй через пару секунд."
    if not state["up"]:
        return "🔴 Сервер недоступен — список администрации получить нельзя."
    if state["players"] is None:
        return f"⚠️ Сервер временно не отдаёт список игроков (онлайн: {(state['info'] or {}).get('online', '?')})."
    online = sorted((p for p in state["players"] if p["name"].lower() in ADMINS_LOWER),
                    key=lambda p: p["name"].lower())
    lines = [f"👮 Администрация онлайн: {len(online)}/{len(ADMINS)}\n"]
    for p in online:
        rk = rank_of(p["name"])
        suffix = f" — {html_mod.escape(rk)}" if rk else ""
        lines.append(f"🟢 {html_mod.escape(p['name'])} [ID {p['id']}]{suffix}")
    if not online:
        lines.append("Сейчас никого нет в сети.")
    return "\n".join(lines)


def cmd_players(staff: bool) -> str:
    if state["up"] is None:
        return "⏳ Данные ещё загружаются, попробуй через пару секунд."
    if not state["up"]:
        return "🔴 Сервер недоступен."
    if state["players"] is None:
        online = (state["info"] or {}).get("online", "?")
        return f"⚠️ Сервер временно не отдаёт список игроков (онлайн: {online}). Попробуй позже."
    ps = [p for p in state["players"] if staff or p["name"].lower() not in SPECIAL_ADMINS]
    ps.sort(key=lambda p: p["id"])
    lines = [f"👥 Игроки онлайн: {len(ps)}\n"]
    for p in ps:
        mark = "👮" if staff and p["name"].lower() in ADMINS_LOWER else "•"
        lines.append(f"{mark} {html_mod.escape(p['name'])} [{p['id']}]")
    return "\n".join(lines)


def cmd_server(uid: int = None, show_trackers: bool = True) -> str:
    if state["up"] is None:
        return "⏳ Данные ещё загружаются, попробуй через пару секунд."
    up = bool(state["up"])
    info = state["info"] or {}
    rules = info.get("rules", {})
    name = info.get("hostname") or SERVER_NAME
    lines = [f"{'🟢' if up else '🔴'} {html_mod.escape(name)}",
             f"🌐 Адрес: {SERVER_HOST}:{SERVER_PORT}"]
    if up:
        o, mx = info.get("online", 0), info.get("max", 0) or 1
        filled = max(0, min(10, round(o / mx * 10)))
        lines.append(f"👥 Онлайн: {o}/{info.get('max', '?')} {'▰' * filled}{'▱' * (10 - filled)}")
    else:
        since = f" уже {fmt_dur(now() - state['since'])}" if state["since"] else ""
        lines.append(f"👥 Онлайн: — (сервер недоступен{since})")
    peak = db_one("SELECT MAX(online) FROM history WHERE ts >= ?", (now() - STATS_HOURS * 3600,))
    lines.append(f"📈 Пик за {STATS_HOURS}ч: {peak[0] if peak and peak[0] is not None else '—'}")
    lines.append(f"🔑 Доступ: {'закрытый (под паролем)' if info.get('passworded') else 'свободный'}")
    lines.append(f"📝 Игровой мод: {html_mod.escape(info.get('gamemode') or '—')}")
    lines.append(f"🌍 Язык: {html_mod.escape(info.get('language') or '—')}")
    lines.append(f"🔗 Сайт: {html_mod.escape(rules.get('weburl') or '—')}")
    lines.append(f"⚙️ Версия SA-MP: {html_mod.escape(rules.get('version') or '—')}")
    lines.append(f"🕒 Обновлено: {ago(state['last_ok']) if state['last_ok'] else '—'}")
    if up and state["players"] is not None:
        adm = sum(1 for p in state["players"] if p["name"].lower() in ADMINS_LOWER)
        lines.append(f"👮 Администраторов онлайн: {adm} из {len(ADMINS)}")

    ds = day_start_ts()
    row = db_one(
        "SELECT MAX(online), AVG(online), MIN(online), MAX(admins), COUNT(*), MIN(ts) "
        "FROM history WHERE ts >= ?", (ds,))
    if row:
        mx_, avg, mn, adm_mx, cnt, first_ts = row
        lines.append(f"\n📅 Серверные сутки с {DAY_START_HOUR:02d}:00 МСК (сброс через {fmt_dur(ds + 86400 - now())})")
        if cnt:
            peak_ts = db_one("SELECT ts FROM history WHERE ts >= ? ORDER BY online DESC, ts ASC LIMIT 1", (ds,))[0]
            lines += [f"Максимум онлайна: {mx_} (в {fmt_hm(peak_ts)})",
                      f"Средний онлайн: {round(avg)} | минимум: {mn}",
                      f"Максимум админов онлайн: {adm_mx}"]
            if first_ts - ds > 300:
                lines.append(f"ℹ️ Данные собираются с {fmt_hm(first_ts)} — бот был запущен позже начала суток.")
        else:
            lines.append("Данных за эти сутки пока нет.")
        prev = db_one("SELECT MAX(online) FROM history WHERE ts >= ? AND ts < ?", (ds - 86400, ds))
        if prev and prev[0] is not None:
            lines.append(f"Прошлые сутки: максимум {prev[0]}")
    if uid and show_trackers:
        lines.append(f"\n🔔 Трекеры: {tracker_count(uid)}/{MAX_TRACKS}")
    return "\n".join(lines)


def cmd_stats() -> str:
    def q(sql, *a):
        return (db_one(sql, a) or [0])[0] or 0
    return (
        "📊 Статистика бота\n\n"
        f"Пользователей всего: {q('SELECT COUNT(*) FROM users')}\n"
        f"Активных за 24 ч: {q('SELECT COUNT(*) FROM users WHERE last_seen > ?', now() - 86400)}\n"
        f"Новых за 24 ч: {q('SELECT COUNT(*) FROM users WHERE first_seen > ?', now() - 86400)}\n"
        f"Доступ разрешён: {q('SELECT COUNT(*) FROM allowed_users')} (плюс админы и основатель)\n"
        f"Заблокировано: {q('SELECT COUNT(*) FROM blocked')}\n"
        f"Админов бота: {q('SELECT COUNT(*) FROM bot_admins')}\n"
        f"Всего запросов: {q('SELECT SUM(requests) FROM users')}\n"
        f"Игроков в базе мониторинга: {q('SELECT COUNT(*) FROM players')}\n"
        f"Трекеров (личных): {q('SELECT COUNT(*) FROM tracks') + q('SELECT COUNT(*) FROM online_tracks') + q('SELECT COUNT(*) FROM event_tracks')}\n"
        f"Трекеров бесед: {q('SELECT COUNT(*) FROM chat_tracks')}\n"
        f"Бесед: {q('SELECT COUNT(*) FROM chat_settings')}\n"
        f"Аптайм бота: {fmt_dur(now() - START_TS)}")


# ═══════════════════════ ИГРОКИ ═══════════════════════
def play_seconds(low: str, start: int, end: int) -> int:
    t = now()
    rows = db_all("SELECT join_ts, COALESCE(leave_ts, ?) FROM sessions "
                  "WHERE name_lower=? AND join_ts < ? AND COALESCE(leave_ts, ?) > ?",
                  (t, low, end, t, start))
    return sum(max(0, min(l, end, t) - max(j, start)) for j, l in rows)


def pstats_text(name: str) -> str:
    low = name.lower()
    row = db_one("SELECT name, online, last_join, last_leave, score FROM players WHERE name_lower=?", (low,))
    if not row:
        return "🤷 Этого игрока бот ещё не видел на сервере."
    pname, online, last_join, last_leave, score = row
    ds = day_start_ts()
    lines = [f"📊 <b>{html_mod.escape(pname)}</b> — статистика за {PROFILE_DAYS} игровых дней",
             f"(сутки считаются с {DAY_START_HOUR:02d}:00 МСК)\n"]
    total = 0
    for i in range(PROFILE_DAYS):
        start = ds - i * 86400
        secs = play_seconds(low, start, start + 86400)
        total += secs
        label = datetime.fromtimestamp(start, TZ).strftime("%d.%m")
        if i == 0:
            label += " (сегодня)"
        elif i == 1:
            label += " (вчера)"
        lines.append(f"{label}: {fmt_dur(secs) if secs >= 60 else '—'}")
    lines.append(f"\nВсего за {PROFILE_DAYS} дн.: {fmt_dur(total) if total >= 60 else '—'}")
    lines.append(f"Уровень: {score if score is not None else 'неизвестно'}")
    lines.append(f"Статус: {'🟢 в сети' if online else '⚫ не в сети'}")
    if last_join:
        lines.append(f"Последний заход: {fmt_dt(last_join)}")
    if last_leave and not online:
        lines.append(f"Последний выход: {fmt_dt(last_leave)}")
    since = int(kv_get("monitor_since") or now())
    if since > ds - (PROFILE_DAYS - 1) * 86400:
        lines.append(f"\nℹ️ Бот ведёт учёт с {fmt_dt(since)} (МСК) — раньше данных нет.")
    lines.append("Время считается по тому, когда бот видел игрока на сервере (точность ~15 сек).")
    return "\n".join(lines)


def player_card(row) -> str:
    name, online, last_join, last_leave = row[1], row[2], row[3], row[4]
    score = row[6] if len(row) > 6 else None
    lines = [f"{'🟢' if online else '⚫'} <b>{html_mod.escape(name)}</b>",
             f"Статус: {'в сети' if online else 'не в сети'}"]
    if online:
        live = next((p for p in (state["players"] or []) if p["name"].lower() == name.lower()), None)
        if live:
            lines.append(f"ID: {live['id']} | Пинг: {live['ping']}")
        if last_join:
            lines.append(f"Подключился: {fmt_dt(last_join)} ({fmt_dur(now() - last_join)} назад)")
    else:
        if last_join:
            lines.append(f"Последнее подключение: {fmt_dt(last_join)}")
        if last_leave:
            lines.append(f"Последнее отключение: {fmt_dt(last_leave)} ({fmt_dur(now() - last_leave)} назад)")
    if score is not None:
        lines.append(f"Уровень: {score}")
    return "\n".join(lines) + "\n\nВремя — по МСК."


def lookup(uid: int, text: str):
    q = text.strip().replace(" ", "_").lower()
    if len(q) < 2 or len(q) > 24:
        return "Введи ник игрока, например Laurent_Sykes.", None
    if q in SPECIAL_ADMINS and not is_staff(uid):
        return "🤷 Такого игрока бот ещё не видел на сервере.", None
    exact = db_one("SELECT * FROM players WHERE name_lower=?", (q,))
    if exact:
        return player_card(exact), exact[1]
    like = db_all("SELECT * FROM players WHERE name_lower LIKE ? ORDER BY online DESC, last_seen DESC LIMIT 8",
                  (f"%{q}%",))
    if not is_staff(uid):
        like = [r for r in like if r[1].lower() not in SPECIAL_ADMINS]
    if len(like) == 1:
        return player_card(like[0]), like[0][1]
    if like:
        return ("Нашёл несколько похожих ников, уточни:\n\n" +
                "\n".join(f"{'🟢' if r[2] else '⚫'} {html_mod.escape(r[1])}" for r in like)), None
    return (f"🤷 Такого игрока бот ещё не видел на сервере. Возможно, он не заходил с момента "
            f"запуска мониторинга или ник написан с ошибкой.\n"
            f"Чтобы получить уведомление, когда он появится: /track {text.strip()}"), None


# ═══════════════════════ АВТООТЧЁТЫ ═══════════════════════
def build_auto_report(uid: int) -> str:
    lines = [f"🔔 Автоотчёт — {fmt_dt(now())} (МСК)\n"]
    if state["up"] is None:
        return lines[0] + "Данные ещё загружаются."
    if not state["up"]:
        since = f" (уже {fmt_dur(now() - state['since'])})" if state["since"] else ""
        lines.append(f"🔴 Сервер недоступен{since}")
    else:
        i = state["info"]
        lines.append(f"🟢 Онлайн сервера: {i['online']}/{i['max']}")
        if state["players"] is None:
            lines.append("⚠️ Список игроков недоступен (сервер не отдаёт).")
        else:
            adm = sorted((p["name"] for p in state["players"] if p["name"].lower() in ADMINS_LOWER),
                         key=str.lower)
            lines.append(f"👮 Администраторов онлайн: {len(adm)} из {len(ADMINS)}")
            if adm:
                lines.append(", ".join(html_mod.escape(x) for x in adm))
    ds = day_start_ts()
    mx = db_one("SELECT MAX(online) FROM history WHERE ts >= ?", (ds,))
    if mx and mx[0] is not None:
        lines.append(f"📈 Максимум за серверные сутки: {mx[0]}")
    tr = db_all("SELECT t.name, p.online, p.last_leave FROM tracks t "
                "LEFT JOIN players p ON p.name_lower = t.name_lower "
                "WHERE t.user_id=? ORDER BY t.name", (uid,))
    if tr:
        lines.append("\n👁 Игроки из твоего трекера:")
        for name, online, last_leave in tr:
            if online:
                lines.append(f"🟢 {html_mod.escape(name)} — в сети")
            elif last_leave:
                lines.append(f"⚫ {html_mod.escape(name)} — не в сети (вышел {ago(last_leave)})")
            else:
                lines.append(f"⚫ {html_mod.escape(name)} — не в сети")
    lines.append("\nОтключить: /autoinfo")
    return "\n".join(lines)


# ═══════════════════════ КЛАВИАТУРЫ ═══════════════════════
def kb_main(staff: bool) -> ReplyKeyboardMarkup:
    rows = [
        [KeyboardButton(text="Сервер"), KeyboardButton(text="Игроки")],
        [KeyboardButton(text="Профиль"), KeyboardButton(text="Трекер")],
    ]
    if staff:
        rows.append([KeyboardButton(text="Админы"), KeyboardButton(text="Автоотчёт")])
    return ReplyKeyboardMarkup(keyboard=rows, resize_keyboard=True)


def kb_card(name: str, uid: int) -> InlineKeyboardMarkup:
    follow = "🔕 Не следить" if is_tracked(uid, name) else "🔔 Следить"
    action = "untrack" if is_tracked(uid, name) else "track"
    return InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text=follow, callback_data=f"{action}:{name}"),
        InlineKeyboardButton(text="📊 За 7 дней", callback_data=f"pstats:{name}"),
    ]])


TEXT_TO_ACTION = {
    "сервер": "server", "игроки": "players", "профиль": "profile",
    "трекер": "tracklist", "админы": "admins", "автоотчёт": "auto",
    "автоотчет": "auto", "меню": "menu", "кнопки": "menu",
}


# ═══════════════════════ ХЕНДЛЕРЫ ═══════════════════════
async def _guard(msg: Message) -> bool:
    uid = msg.from_user.id if msg.from_user else 0
    if is_maintenance() and not is_owner(uid):
        await msg.answer(get_maint_text())
        return False
    if not has_access(uid):
        return False
    if db_one("SELECT 1 FROM blocked WHERE user_id=?", (uid,)):
        return False
    t = now()
    db_exec("INSERT INTO users(user_id,first_seen,last_seen,requests) VALUES(?,?,?,1) "
            "ON CONFLICT(user_id) DO UPDATE SET last_seen=?, requests=requests+1", (uid, t, t, t))
    return True


@router.message(CommandStart())
async def h_start(msg: Message):
    if not await _guard(msg):
        return
    uid = msg.from_user.id
    await msg.answer(cmd_start(uid), reply_markup=kb_main(is_staff(uid)))


@router.message(Command("menu"))
async def h_menu(msg: Message):
    if not await _guard(msg):
        return
    await msg.answer("Кнопки включены 👇", reply_markup=kb_main(is_staff(msg.from_user.id)))


@router.message(Command("hidekb"))
async def h_hidekb(msg: Message):
    if not await _guard(msg):
        return
    await msg.answer("Кнопки скрыты. Вернуть: /menu", reply_markup=ReplyKeyboardRemove())


@router.message(Command("logs"))
async def h_logs(msg: Message):
    if not await _guard(msg):
        return
    await send_long(msg.chat.id, cmd_logs())


@router.message(Command("stats"))
async def h_stats(msg: Message):
    if not await _guard(msg):
        return
    await msg.answer(cmd_stats())


@router.message(Command("chatid"))
async def h_chatid(msg: Message):
    if not await _guard(msg):
        return
    if msg.chat.type == "private":
        await msg.answer("Это команда для беседы.")
        return
    await msg.answer(f"🆔 ID этой беседы: <code>{msg.chat.id}</code>\n\n"
                     f"Отправь основателю в ЛС:\n"
                     f"<code>/setchatadmin {msg.chat.id} {msg.from_user.id}</code>")


@router.message(Command("server"))
async def h_server(msg: Message):
    if not await _guard(msg):
        return
    text = cmd_server(msg.from_user.id, show_trackers=msg.chat.type == "private")
    if msg.chat.type == "private":
        path = await asyncio.to_thread(build_chart_sync)
        if path and os.path.exists(path):
            await msg.answer_photo(FSInputFile(path), caption=text[:1024])
            return
    await msg.answer(text)


@router.message(Command("players"))
async def h_players(msg: Message):
    if not await _guard(msg):
        return
    await send_long(msg.chat.id, cmd_players(is_staff(msg.from_user.id)))


@router.message(Command("admins"))
async def h_admins(msg: Message):
    if not await _guard(msg):
        return
    if not is_staff(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    await send_long(msg.chat.id, cmd_admins())


@router.message(Command("autoinfo"))
async def h_auto(msg: Message):
    if not await _guard(msg):
        return
    uid = msg.from_user.id
    if not is_staff(uid):
        await msg.answer("Неизвестная команда.")
        return
    if db_one("SELECT 1 FROM auto_notify WHERE user_id=?", (uid,)):
        db_exec("DELETE FROM auto_notify WHERE user_id=?", (uid,))
        await msg.answer("🔕 Автоотчёты выключены.")
        return
    db_exec("INSERT INTO auto_notify VALUES(?,?)", (uid, now()))
    await msg.answer(build_auto_report(uid))
    await msg.answer("🔔 Автоотчёты включены: каждые 30 минут буду присылать данные о сервере.")


@router.message(Command("nickchanges"))
async def h_nickchanges(msg: Message):
    if not await _guard(msg):
        return
    uid = msg.from_user.id
    if not is_staff(uid):
        await msg.answer("Неизвестная команда.")
        return
    if db_one("SELECT 1 FROM nick_watchers WHERE user_id=?", (uid,)):
        db_exec("DELETE FROM nick_watchers WHERE user_id=?", (uid,))
        await msg.answer("🔕 Уведомления о смене ников ВЫКЛЮЧЕНЫ.")
    else:
        db_exec("INSERT INTO nick_watchers VALUES(?)", (uid,))
        await msg.answer("🔔 Уведомления о смене ников ВКЛЮЧЕНЫ. Буду присылать сюда.")


@router.message(Command("regstats"))
async def h_regstats(msg: Message):
    if not await _guard(msg):
        return
    if not is_staff(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    start = day_start_ts()
    cnt = (db_one("SELECT COUNT(*) FROM registrations WHERE ts >= ?", (start,)) or [0])[0] or 0
    await msg.answer(f"📊 За эти сутки зарегистрировалось: {cnt} чел.")


@router.message(Command("greetings"))
async def h_greetings(msg: Message):
    if not await _guard(msg):
        return
    uid = msg.from_user.id
    if not is_staff(uid):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2:
        await msg.answer("Использование: /greetings on|off")
        return
    if arg[1].lower() in ("on", "вкл", "1"):
        db_exec("INSERT OR IGNORE INTO greet_watchers(user_id) VALUES(?)", (uid,))
        db_exec("UPDATE greet_watchers SET morning=1, night=1 WHERE user_id=?", (uid,))
        await msg.answer("✅ Приветствия ВКЛЮЧЕНЫ.")
    else:
        db_exec("DELETE FROM greet_watchers WHERE user_id=?", (uid,))
        await msg.answer("🔕 Приветствия ВЫКЛЮЧЕНЫ.")


@router.message(Command("maintenance"))
async def h_maintenance(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2 or not arg[1].isdigit():
        await msg.answer("Использование: /maintenance <минут>\n0 - выключить.")
        return
    mins = int(arg[1])
    if mins == 0:
        kv_set("maint_end", 0)
        await msg.answer("🟢 Тех.обслуживание ВЫКЛЮЧЕНО.")
    else:
        kv_set("maint_end", now() + mins * 60)
        await msg.answer(f"🟠 Тех.обслуживание включено на {mins} мин.")


@router.message(Command("setforumnick"))
async def h_setforumnick(msg: Message):
    if not await _guard(msg):
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2:
        await msg.answer("Использование: /setforumnick Ник")
        return
    nick = arg[1].strip()
    db_exec("INSERT OR REPLACE INTO forum_nicks(user_id, nick, enabled) VALUES(?,?,1)",
            (msg.from_user.id, nick))
    await msg.answer(f"✅ Теперь я слежу за жалобами на <b>{html_mod.escape(nick)}</b> на форуме.")


@router.message(Command("forumoff"))
async def h_forumoff(msg: Message):
    if not await _guard(msg):
        return
    db_exec("UPDATE forum_nicks SET enabled=0 WHERE user_id=?", (msg.from_user.id,))
    await msg.answer("🔕 Уведомления о жалобах с форума отключены.")


@router.message(Command("setnick"))
async def h_setnick(msg: Message):
    if not await _guard(msg):
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2:
        await msg.answer("Использование: /setnick Ник_Фамилия")
        return
    nick = arg[1].replace(" ", "_")
    if not NICK_RE.match(nick):
        await msg.answer("Некорректный ник.")
        return
    db_exec("UPDATE users SET nick=? WHERE user_id=?", (nick, msg.from_user.id))
    await msg.answer(f"✅ Ник <b>{html_mod.escape(nick)}</b> привязан. /profile покажет статистику.")


@router.message(Command("profile"))
async def h_profile(msg: Message):
    if not await _guard(msg):
        return
    row = db_one("SELECT nick FROM users WHERE user_id=?", (msg.from_user.id,))
    if not row or not row[0]:
        await msg.answer("Сначала привяжи свой ник: /setnick Ник_Фамилия")
        return
    await send_long(msg.chat.id, pstats_text(row[0]))


@router.message(Command("pstats"))
async def h_pstats(msg: Message):
    if not await _guard(msg):
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2:
        await msg.answer("Использование: /pstats Ник_Фамилия")
        return
    await send_long(msg.chat.id, pstats_text(arg[1].replace(" ", "_")))


@router.message(Command("track"))
async def h_track(msg: Message):
    if not await _guard(msg):
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2:
        await msg.answer("Использование: /track Ник")
        return
    nick = arg[1].replace(" ", "_")
    if not NICK_RE.match(nick):
        await msg.answer("Некорректный ник.")
        return
    await msg.answer(cmd_track(msg.from_user.id, arg[1]))


@router.message(Command("untrack"))
async def h_untrack(msg: Message):
    if not await _guard(msg):
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2:
        await msg.answer("Использование: /untrack Ник")
        return
    await msg.answer(cmd_untrack(msg.from_user.id, arg[1]))


@router.message(Command("trackonline"))
async def h_trackonline(msg: Message):
    if not await _guard(msg):
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2:
        await msg.answer("Использование: /trackonline число")
        return
    await msg.answer(cmd_trackonline(msg.from_user.id, arg[1]))


@router.message(Command("untrackonline"))
async def h_untrackonline(msg: Message):
    if not await _guard(msg):
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2:
        await msg.answer("Использование: /untrackonline число")
        return
    await msg.answer(cmd_untrackonline(msg.from_user.id, arg[1]))


@router.message(Command("tracklist"))
async def h_tracklist(msg: Message):
    if not await _guard(msg):
        return
    if msg.chat.type != "private":
        await msg.answer(cmd_chat_tracklist(msg.chat.id))
    else:
        await send_long(msg.chat.id, cmd_tracklist(msg.from_user.id))


@router.message(Command("trackonlinefall"))
async def h_trackonlinefall(msg: Message):
    if not await _guard(msg):
        return
    if msg.chat.type == "private":
        await msg.answer("Команда работает в беседах.")
        return
    if not is_chat_admin(msg.from_user.id, msg.chat.id):
        await msg.answer("Трекерами беседы управляет только её админ или основатель.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2 or not arg[1].isdigit():
        await msg.answer("Использование: /trackonlinefall N")
        return
    await msg.answer(chat_add_track(msg.chat.id, "online_fall", str(int(arg[1])), msg.from_user.id))


@router.message(Command("untrackonlinefall"))
async def h_untrackonlinefall(msg: Message):
    if not await _guard(msg):
        return
    if msg.chat.type == "private":
        await msg.answer("Команда работает в беседах.")
        return
    if not is_chat_admin(msg.from_user.id, msg.chat.id):
        await msg.answer("Трекерами беседы управляет только её админ или основатель.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2 or not arg[1].isdigit():
        await msg.answer("Использование: /untrackonlinefall N")
        return
    await msg.answer(chat_del_track(msg.chat.id, "online_fall", str(int(arg[1]))))


@router.message(Command("trackevent"))
async def h_trackevent(msg: Message):
    if not await _guard(msg):
        return
    if msg.chat.type == "private":
        await msg.answer("Команда работает в беседах.")
        return
    if not is_chat_admin(msg.from_user.id, msg.chat.id):
        await msg.answer("Трекерами беседы управляет только её админ или основатель.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2 or arg[1].lower() not in CHAT_EVENTS:
        await msg.answer("Использование: /trackevent down|up|mod")
        return
    await msg.answer(chat_add_track(msg.chat.id, arg[1].lower(), "", msg.from_user.id))


@router.message(Command("untrackevent"))
async def h_untrackevent(msg: Message):
    if not await _guard(msg):
        return
    if msg.chat.type == "private":
        await msg.answer("Команда работает в беседах.")
        return
    if not is_chat_admin(msg.from_user.id, msg.chat.id):
        await msg.answer("Трекерами беседы управляет только её админ или основатель.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2 or arg[1].lower() not in CHAT_EVENTS:
        await msg.answer("Использование: /untrackevent down|up|mod")
        return
    await msg.answer(chat_del_track(msg.chat.id, arg[1].lower(), ""))


# ───── owner-команды ─────
async def _resolve_target(msg: Message, arg: str):
    if msg.reply_to_message and msg.reply_to_message.from_user:
        return msg.reply_to_message.from_user.id
    arg = arg.lstrip("@")
    if re.fullmatch(r"\d+", arg):
        return int(arg)
    await msg.answer("Укажи ID или @username, либо ответь (reply) на сообщение пользователя.")
    return None


@router.message(Command("allow"))
async def h_allow(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    a = arg[1] if len(arg) > 1 else ""
    target = await _resolve_target(msg, a)
    if not target:
        return
    db_exec("INSERT OR IGNORE INTO allowed_users VALUES(?,?,?)", (target, msg.from_user.id, now()))
    await msg.answer(f"✅ id{target} получил доступ к боту.")


@router.message(Command("deny"))
async def h_deny(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    a = arg[1] if len(arg) > 1 else ""
    target = await _resolve_target(msg, a)
    if not target:
        return
    db_exec("DELETE FROM allowed_users WHERE user_id=?", (target,))
    await msg.answer(f"✅ Доступ id{target} закрыт.")


@router.message(Command("allowlist"))
async def h_allowlist(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    rows = db_all("SELECT user_id FROM allowed_users")
    if not rows:
        await msg.answer("В белом списке никого нет.")
        return
    await msg.answer("👥 Пользователи с доступом:\n" + "\n".join(f"• id{r[0]}" for r in rows))


@router.message(Command("block"))
async def h_block(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    a = arg[1] if len(arg) > 1 else ""
    target = await _resolve_target(msg, a)
    if not target:
        return
    if target == OWNER_ID:
        await msg.answer("Основателя это не касается 🙂")
        return
    db_exec("INSERT OR REPLACE INTO blocked VALUES(?,?)", (target, now()))
    db_exec("DELETE FROM bot_admins WHERE user_id=?", (target,))
    await msg.answer(f"⛔ id{target} заблокирован.")


@router.message(Command("unblock"))
async def h_unblock(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    a = arg[1] if len(arg) > 1 else ""
    target = await _resolve_target(msg, a)
    if not target:
        return
    n = db_exec("DELETE FROM blocked WHERE user_id=?", (target,))
    await msg.answer(f"✅ id{target} разблокирован." if n else "Не был заблокирован.")


@router.message(Command("newadm"))
async def h_newadm(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    a = arg[1] if len(arg) > 1 else ""
    target = await _resolve_target(msg, a)
    if not target:
        return
    if db_one("SELECT 1 FROM bot_admins WHERE user_id=?", (target,)):
        await msg.answer(f"id{target} уже админ бота.")
        return
    db_exec("DELETE FROM blocked WHERE user_id=?", (target,))
    db_exec("INSERT INTO bot_admins VALUES(?,?,?)", (target, msg.from_user.id, now()))
    await msg.answer(f"✅ id{target} назначен админом бота.")


@router.message(Command("deladm"))
async def h_deladm(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    a = arg[1] if len(arg) > 1 else ""
    target = await _resolve_target(msg, a)
    if not target:
        return
    n = db_exec("DELETE FROM bot_admins WHERE user_id=?", (target,))
    db_exec("DELETE FROM auto_notify WHERE user_id=?", (target,))
    await msg.answer(f"✅ id{target} больше не админ бота." if n else "Он не был админом бота.")


@router.message(Command("admlist"))
async def h_admlist(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    rows = db_all("SELECT user_id FROM bot_admins")
    if not rows:
        await msg.answer("Админов бота нет.")
        return
    await msg.answer("👮 Админы бота:\n" + "\n".join(f"id{r[0]}" for r in rows))


@router.message(Command("chats"))
async def h_chats(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    await send_long(msg.chat.id, cmd_chats())


@router.message(Command("setchatadmin"))
async def h_setchatadmin(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=2)
    if len(arg) < 3 or not arg[1].lstrip("-").isdigit():
        await msg.answer("Использование: /setchatadmin <chat_id> <id|@username>\n"
                         "Или: /setchatadmin <chat_id> (reply на нужного человека)")
        return
    chat_id = int(arg[1])
    if chat_id not in all_chat_ids():
        await msg.answer(f"Беседа {chat_id} боту неизвестна. Добавь бота и напиши там /chatid.")
        return
    target = await _resolve_target(msg, arg[2] if len(arg) > 2 else "")
    if not target:
        return
    db_exec("INSERT OR REPLACE INTO chat_admins VALUES(?,?,?)", (chat_id, target, now()))
    await msg.answer(f"✅ id{target} назначен админом беседы {chat_id}.")


@router.message(Command("delchatadmin"))
async def h_delchatadmin(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2 or not arg[1].lstrip("-").isdigit():
        await msg.answer("Использование: /delchatadmin <chat_id>")
        return
    chat_id = int(arg[1])
    n = db_exec("DELETE FROM chat_admins WHERE chat_id=?", (chat_id,))
    await msg.answer(f"✅ Админ беседы {chat_id} снят." if n else "У беседы не было админа.")


@router.message(Command("setrank"))
async def h_setrank(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=2)
    if len(arg) < 3:
        await msg.answer("Использование: /setrank Ник Ранг")
        return
    nick, rk = arg[1].replace(" ", "_"), arg[2].strip()
    if nick.lower() not in ADMINS_LOWER:
        await msg.answer(f"{nick} нет в списке админов сервера.")
        return
    db_exec("INSERT OR REPLACE INTO admin_ranks VALUES(?,?)", (nick.lower(), rk))
    await msg.answer(f"✅ Ранг для {nick}: {html_mod.escape(rk)}")


@router.message(Command("delrank"))
async def h_delrank(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2:
        await msg.answer("Использование: /delrank Ник")
        return
    nick = arg[1].replace(" ", "_").lower()
    n = db_exec("DELETE FROM admin_ranks WHERE name_lower=?", (nick,))
    await msg.answer("✅ Ранг удалён." if n else "У этого ника не было ранга.")


@router.message(Command("broadcast"))
async def h_broadcast(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        await msg.answer("Неизвестная команда.")
        return
    arg = (msg.text or "").split(maxsplit=1)
    if len(arg) < 2:
        await msg.answer("Использование: /broadcast текст")
        return
    await _start_broadcast(msg, arg[1], "")


async def _start_broadcast(msg: Message, text: str, att: str):
    bid = secrets.token_hex(3)
    pending_bc[msg.from_user.id] = {"id": bid, "text": text, "att": att, "ts": now()}
    kb = InlineKeyboardMarkup(inline_keyboard=[[
        InlineKeyboardButton(text="✅ Разослать", callback_data=f"bc_ok:{bid}"),
        InlineKeyboardButton(text="❌ Отмена", callback_data=f"bc_no:{bid}"),
    ]])
    total = (db_one("SELECT COUNT(*) FROM users WHERE user_id NOT IN (SELECT user_id FROM blocked)") or [0])[0]
    await msg.answer(f"📣 Предпросмотр. Получателей: {total}\n\n{text[:3500] if text else ''}",
                     reply_markup=kb)


pending_bc = {}


@router.callback_query(F.data.startswith("bc_"))
async def h_bc(cb: CallbackQuery):
    if not is_owner(cb.from_user.id):
        await cb.answer("Нельзя.")
        return
    action, bid = cb.data.split(":", 1)
    pb = pending_bc.get(cb.from_user.id)
    if not pb or pb["id"] != bid or now() - pb["ts"] > 600:
        await cb.message.answer("Рассылка устарела.")
        await cb.answer()
        return
    pending_bc.pop(cb.from_user.id, None)
    if action == "bc_no":
        await cb.message.answer("❌ Отменено.")
        await cb.answer()
        return
    await cb.message.answer("📤 Рассылаю…")
    await cb.answer()
    await run_broadcast(cb.from_user.id, pb["text"], pb["att"])


async def run_broadcast(owner: int, text: str, att: str):
    ids = [r[0] for r in db_all("SELECT user_id FROM users WHERE user_id NOT IN (SELECT user_id FROM blocked)")]
    ok = fail = 0
    for i in range(0, len(ids), 25):
        batch = ids[i:i + 25]
        for uid in batch:
            try:
                await bot.send_message(uid, (text or "")[:4000], disable_web_page_preview=True)
                ok += 1
            except Exception:
                fail += 1
            await asyncio.sleep(0.05)
        await asyncio.sleep(0.5)
    await bot.send_message(owner, f"📣 Рассылка завершена.\nДоставлено: {ok}\nНе доставлено: {fail}")


# ───── карточка игрока: callbacks ─────
@router.callback_query(F.data.startswith("track:"))
async def cb_track(cb: CallbackQuery):
    if not await _cb_guard(cb):
        return
    name = cb.data.split(":", 1)[1]
    text = cmd_track(cb.from_user.id, name)
    await cb.message.answer(text, reply_markup=kb_card(name, cb.from_user.id))
    await cb.answer()


@router.callback_query(F.data.startswith("untrack:"))
async def cb_untrack(cb: CallbackQuery):
    if not await _cb_guard(cb):
        return
    name = cb.data.split(":", 1)[1]
    text = cmd_untrack(cb.from_user.id, name)
    await cb.message.answer(text, reply_markup=kb_card(name, cb.from_user.id))
    await cb.answer()


@router.callback_query(F.data.startswith("pstats:"))
async def cb_pstats(cb: CallbackQuery):
    if not await _cb_guard(cb):
        return
    name = cb.data.split(":", 1)[1]
    await send_long(cb.message.chat.id, pstats_text(name))
    await cb.answer()


async def _cb_guard(cb: CallbackQuery) -> bool:
    uid = cb.from_user.id
    if is_maintenance() and not is_owner(uid):
        await cb.answer(get_maint_text(), show_alert=True)
        return False
    if not has_access(uid) or db_one("SELECT 1 FROM blocked WHERE user_id=?", (uid,)):
        await cb.answer("Нет доступа.")
        return False
    return True


# ───── универсальный хендлер: текст, кнопки, ник ─────
@router.message(F.text)
async def h_text(msg: Message):
    if not await _guard(msg):
        return
    uid = msg.from_user.id
    text = msg.text.strip()

    if is_maintenance() and not is_owner(uid):
        return

    low = text.lower()

    # кнопки Reply
    if low in TEXT_TO_ACTION:
        action = TEXT_TO_ACTION[low]
        if action == "server":
            return await h_server(msg)
        if action == "players":
            return await h_players(msg)
        if action == "profile":
            return await h_profile(msg)
        if action == "tracklist":
            return await h_tracklist(msg)
        if action == "admins":
            return await h_admins(msg)
        if action == "auto":
            return await h_auto(msg)
        if action == "menu":
            return await h_menu(msg)

    # в беседе — игнорируем обычные сообщения
    if msg.chat.type != "private":
        return

    # если это пересланное сообщение / с картинкой — предложить рассылку (только owner)
    if is_owner(uid):
        if msg.photo or msg.video or msg.document or msg.audio or msg.voice:
            return
        if msg.forward_origin:
            return

    # ищем игрока
    text_out, name = lookup(uid, text)
    if name:
        await msg.answer(text_out, reply_markup=kb_card(name, uid))
    else:
        await msg.answer(text_out)


@router.message(F.photo | F.video | F.document | F.audio | F.voice)
async def h_media(msg: Message):
    if not await _guard(msg):
        return
    if not is_owner(msg.from_user.id):
        return
    if msg.chat.type != "private":
        return
    text = msg.caption or ""
    await msg.answer("📣 Медиа-рассылка из TG не поддерживается автоматически. "
                     "Пришли текст через /broadcast.")


# ═══════════════════════ ФОНОВЫЕ ЦИКЛЫ ═══════════════════════
async def auto_loop():
    while True:
        try:
            for uid, last in db_all("SELECT user_id, last_sent FROM auto_notify"):
                if not is_staff(uid):
                    db_exec("DELETE FROM auto_notify WHERE user_id=?", (uid,))
                    continue
                if now() - last >= AUTO_INTERVAL:
                    db_exec("UPDATE auto_notify SET last_sent=? WHERE user_id=?", (now(), uid))
                    await notify(uid, build_auto_report(uid))
        except Exception:
            log.exception("Ошибка автоотчётов")
        await asyncio.sleep(30)


async def greet_loop():
    while True:
        try:
            now_dt = datetime.now(TZ)
            h, m = now_dt.hour, now_dt.minute
            if h == 8 and m == 0:
                for (uid,) in db_all("SELECT user_id FROM greet_watchers WHERE morning=1"):
                    await notify(uid, "Доброе утро, мой хозяин! ☀️")
                await asyncio.sleep(60)
            elif h == 22 and m == 0:
                for (uid,) in db_all("SELECT user_id FROM greet_watchers WHERE night=1"):
                    await notify(uid, "Добрых снов, мой хозяин 🌙")
                    db_exec("UPDATE greet_watchers SET night_replied=0 WHERE user_id=?", (uid,))
                await asyncio.sleep(60)
        except Exception:
            log.exception("Ошибка цикла приветствий")
        await asyncio.sleep(30)


# ═══════════════════════ MAIN ═══════════════════════
async def main():
    global _loop
    _loop = asyncio.get_running_loop()

    if not HAVE_MPL:
        log.warning("matplotlib не установлен — график онлайна показываться не будет.")
    if OWNER_ID == 0:
        log.warning("OWNER_ID не задан — команды основателя недоступны.")

    asyncio.create_task(monitor_loop())
    asyncio.create_task(auto_loop())
    asyncio.create_task(greet_loop())

    log.info("Бот запущен (v10.0), слушаю Telegram.")
    await bot.delete_webhook(drop_pending_updates=True)
    await dp.start_polling(bot)


if __name__ == "__main__":
    try:
        asyncio.run(main())
    except (KeyboardInterrupt, SystemExit):
        log.info("Остановлено.")