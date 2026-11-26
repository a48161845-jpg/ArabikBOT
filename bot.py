import asyncio
import copy
import hashlib
import html
import io
import json
import logging
import os
import random
import re
import socket
import time
from collections import Counter, defaultdict
from logging.handlers import RotatingFileHandler
from contextlib import asynccontextmanager, suppress
from contextvars import ContextVar
from datetime import datetime, timedelta, timezone
from difflib import SequenceMatcher
from functools import lru_cache, wraps

from aiogram import Bot, Dispatcher, Router, F
from aiogram.exceptions import TelegramNetworkError, TelegramRetryAfter, TelegramServerError
from aiogram.filters import Command
from aiogram.types import (
    BotCommand,
    BufferedInputFile,
    CallbackQuery,
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    Message,
)
from telethon import TelegramClient, events, utils as tg_utils
from telethon import errors as tl_errors
from telethon.errors import (
    FloodWaitError,
    PeerFloodError,
    PhoneCodeExpiredError,
    PhoneCodeInvalidError,
    RPCError,
    SessionPasswordNeededError,
)
from telethon.tl import functions
from telethon.tl import types as tl_types
from telethon.tl.types import (
    Channel,
    ChannelParticipantsAdmins,
    ChannelParticipantsRecent,
    InputUserEmpty,
    User,
    UserStatusLastMonth,
    UserStatusLastWeek,
    UserStatusOffline,
    UserStatusOnline,
    UserStatusRecently,
)

CONFIG_FILE = "config.json"
PROCESSED_FILE = "processed_users.txt"
DM_STATES_FILE = "dm_states.json"
DM_META_FILE = "dm_meta.json"
REPLY_MAP_FILE = "reply_map.json"
ACC_INFO_FILE = "accounts_info.json"
SPAM_FILE = "spam_state.json"
EVENTS_FILE = "events.jsonl"     # журнал событий для статистики (одна строка = одно событие)
SCHED_FILE = "sched_state.json"      # когда какое расписание уже сработало
SPAM_TZ = timezone(timedelta(hours=7))    # срок спам-блока показываем в МСК+4 (UTC+7); SpamBot отдаёт время в UTC
MSK = timezone(timedelta(hours=3))   # статистика считается по московскому времени (в России нет перехода на летнее)
CHAT_NAMES_FILE = "chat_names.json"
SEEN_FILE = "seen_msgs.json"
DAYLIMIT_FILE = "daylimit_state.json"   # кому сегодня уже выдали ссылку на группу (для суточного лимита)

CONNECT_TIMEOUT = 40        # сек на подключение аккаунта (раньше могло висеть бесконечно и блокировать ВСЕ команды)
ACCEPT_POLL = 15            # как часто (сек) проверять заявки, даже если проверку никто не «разбудил»
STALE_SEC = 6 * 3600        # сообщения старше (бот был офлайн) не получают автоответ — только уведомление вам

log = logging.getLogger("bot")


def setup_logging():
    """Лог в консоль и в bot.log (2 МБ x 3 файла): раньше ошибки в обработке ЛС и автопринятии глотались молча."""
    fmt = logging.Formatter("%(asctime)s %(levelname)s %(name)s: %(message)s", "%d.%m %H:%M:%S")
    root = logging.getLogger()
    root.setLevel(logging.INFO)
    if not root.handlers:
        sh = logging.StreamHandler()
        sh.setFormatter(fmt)
        root.addHandler(sh)
        with suppress(Exception):
            fh = RotatingFileHandler("bot.log", maxBytes=2_000_000, backupCount=2, encoding="utf-8")
            fh.setFormatter(fmt)
            root.addHandler(fh)
    for noisy in ("telethon", "aiogram.event"):
        logging.getLogger(noisy).setLevel(logging.WARNING)

BLANK_ACCOUNT = {"api_id": 0, "api_hash": "", "phone": ""}

DEFAULT_CONFIG = {
    "bot_token": "",  # токен лучше хранить в config.json или переменной BOT_TOKEN
    "admin_ids": [7233257134],
    # Аккаунты по номерам: 1, 2 ... (новые добавляются командой /account N)
    "accounts": {"1": dict(BLANK_ACCOUNT), "2": dict(BLANK_ACCOUNT)},
    # Кто сейчас собирает, а кто отправляет (/collector, /sender, /swap)
    "roles": {"collector": "1", "sender": "2"},
    # Общий список чатов: ref -> режим. src (ИСТ) — откуда берём, bs (БС) — белый список, им не пишем, off (ОТКЛ) — выключен.
    "chat_modes": {},
    "chat_priority": {},       # ref -> "zp" / "kp": приоритет чата (кнопка «Пр» в /chats)
    # ниже — производные списки (считаются из chat_modes при загрузке, руками не править)
    "chat_source_groups": [],
    "chat_exclude_groups": [],
    "messages": ["Привет!"],   # первое сообщение (/text)
    "texts_link": [],          # текст со ссылкой: уходит, когда человек согласился (/text2)
    "texts_refusal": [],       # ответы на отказ, по порядку (/text3)
    "texts_question": [],      # ответы на вопрос, по порядку (/text4)
    "texts_source": [],        # ответы на «откуда контакт», по порядку (/text5)
    "texts_limit": [],         # текст, когда суточный лимит ссылок исчерпан (/text6)
    "daily_link_limit": 5,     # скольким людям в день выдавать ссылку на группу (0 — без лимита, /daylimit)
    "tabs": [{"id": "1", "name": "Вкладка 1"}],   # вкладки для чатов и расписаний
    "chat_tabs": {},           # ref -> id вкладки
    "instance_port": 47213,
    "max_messages": 100,
    "max_inactive_days": 7,
    "scan_messages_limit": 1000,
    "dm_reply_enabled": True,
    "noreply_hours": 24,       # через сколько часов без ответа диалог удаляется у обоих (0 — не удалять)
    "delay_between_messages": 3,
}

# Команда -> (ключ, тип, подсказка)
SETTINGS = {
    "limit": ("max_messages", "int", "Лимит сообщений за запуск (число > 0)"),
    "active": ("max_inactive_days", "int0", "Макс. давность последней активности, дней (0 — не проверять)"),
    "scan": ("scan_messages_limit", "int", "Сколько последних сообщений сканировать в каждом чате"),
    "delay": ("delay_between_messages", "float0", "Пауза между отправками, сек"),
    "wait": ("noreply_hours", "float0", "Через сколько часов без ответа удалять диалог у обоих (0 — не удалять)"),
    "daylimit": ("daily_link_limit", "int0", "Скольким людям в день выдавать ссылку на группу (0 — без лимита). "
                 "Остальным, кто согласился, уйдёт текст из /text6"),
}

# Временные сбои Telegram («internal issues», таймауты) — такие запросы повторяем.
TRANSIENT = tuple(
    getattr(tl_errors, name)
    for name in ("ServerError", "RpcMcgetFailError", "RpcCallFailError", "TimedOutError")
    if hasattr(tl_errors, name)
) + (asyncio.TimeoutError, ConnectionError)


# ---------------------------------------------------------
# Конфиг (с кэшем по времени изменения файла) и файлы
# ---------------------------------------------------------

_cfg_cache = {"stamp": None, "data": None}


def split_variants(text):
    """Старый формат: несколько вариантов текста через строку «---»."""
    return [p.strip() for p in re.split(r"\n\s*-{3,}\s*\n", str(text or "")) if p.strip()]


def save_config(config):
    tmp = CONFIG_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(config, f, ensure_ascii=False, indent=4)
    os.replace(tmp, CONFIG_FILE)
    _cfg_cache["stamp"] = None


# ---- режимы чатов: ИСТ / БС / ОТКЛ ----

CHAT_MODES = ("src", "bs", "off")
MODE_LABEL = {"src": "ИСТ", "bs": "БС", "off": "ОТКЛ"}
MODE_ICON = {"src": "", "bs": "", "off": ""}


def fix_roles(config):
    """Сборщик и отправитель всегда существуют: если аккаунт удалили — роль переходит к свободному."""
    roles = config["roles"]
    for role in ("collector", "sender"):
        if str(roles.get(role)) not in config["accounts"]:
            roles[role] = ""
    if roles["collector"] and roles["collector"] == roles["sender"]:
        roles["sender"] = ""
    free = [s for s in sorted(config["accounts"], key=int) if s not in roles.values()]
    for role in ("collector", "sender"):
        if not roles[role] and free:
            roles[role] = free.pop(0)


def effective_modes(config, slot=None):
    """Режимы чатов: общие, а для аккаунта slot — с его личными поправками (accounts[slot]['chat_modes'])."""
    modes = {str(r): m for r, m in (config.get("chat_modes") or {}).items() if m in CHAT_MODES}
    if slot:
        own = (config["accounts"].get(str(slot)) or {}).get("chat_modes") or {}
        for r, m in own.items():
            if str(r) in modes and m in CHAT_MODES:
                modes[str(r)] = m
    return modes


def account_chats(config, slot=None):
    """-> (источники, белый список БС) для аккаунта slot (или общие)."""
    modes = effective_modes(config, slot)
    return [r for r, m in modes.items() if m == "src"], [r for r, m in modes.items() if m == "bs"]


def derive_chat_lists(config):
    config["chat_source_groups"], config["chat_exclude_groups"] = account_chats(config)


# ---- вкладки: общие для списка чатов и расписаний ----

MAX_TABS = 8


def fix_tabs(config):
    """Вкладки всегда есть (минимум одна); привязки к удалённым вкладкам снимаются."""
    tabs, seen = [], set()
    for t in config.get("tabs") or []:
        if isinstance(t, dict) and t.get("id") and str(t["id"]) not in seen:
            seen.add(str(t["id"]))
            tabs.append({"id": str(t["id"]), "name": str(t.get("name") or f"Вкладка {len(tabs) + 1}")[:24]})
    if not tabs:
        tabs = [{"id": "1", "name": "Вкладка 1"}]
    config["tabs"] = tabs[:MAX_TABS]
    ids = {t["id"] for t in config["tabs"]}
    ct = config.get("chat_tabs")
    config["chat_tabs"] = {str(r): v for r, v in ct.items() if v in ids} if isinstance(ct, dict) else {}


def tab_ids(cfg):
    return [t["id"] for t in cfg["tabs"]]


def tab_name(cfg, tid):
    return next((t["name"] for t in cfg["tabs"] if t["id"] == tid), "?")


def tab_of_chat(cfg, ref):
    t = (cfg.get("chat_tabs") or {}).get(str(ref))
    return t if t in tab_ids(cfg) else cfg["tabs"][0]["id"]


def tab_of_entry(cfg, e):
    t = e.get("tab")
    return t if t in tab_ids(cfg) else cfg["tabs"][0]["id"]


def next_tab(cfg, tid):
    ids = tab_ids(cfg)
    return ids[(ids.index(tid) + 1) % len(ids)] if tid in ids else ids[0]


def load_config():
    try:
        stamp = os.stat(CONFIG_FILE).st_mtime_ns
    except OSError:
        stamp = None
    if stamp is not None and stamp == _cfg_cache["stamp"]:
        return copy.deepcopy(_cfg_cache["data"])

    config = copy.deepcopy(DEFAULT_CONFIG)
    if stamp is None:
        save_config(config)
        return config
    try:
        with open(CONFIG_FILE, "r", encoding="utf-8") as f:
            data = json.load(f)
    except (json.JSONDecodeError, OSError):
        data = {}
    if isinstance(data, dict):
        accounts = data.pop("accounts", None)
        roles = data.pop("roles", None)
        modes_in = data.pop("chat_modes", None)
        legacy = {k: data.pop(k) for k in ("api_id", "api_hash", "phone") if k in data}
        # перенос старых одиночных текстов в новые списки
        if "messages" not in data and data.get("message"):
            data["messages"] = [data["message"]]
        for new, old in (("texts_refusal", "text_refusal"), ("texts_question", "text_question"),
                         ("texts_source", "text_source")):
            if new not in data and data.get(old):
                data[new] = split_variants(data[old])
        config.update(data)
        if isinstance(accounts, dict):
            if "collector" in accounts or "sender" in accounts:
                # Старый формат (collector/sender) -> аккаунты 1 и 2
                accounts = {"1": accounts.get("collector", {}), "2": accounts.get("sender", {})}
                roles = roles or {"collector": "1", "sender": "2"}
            config["accounts"] = {}      # берём ровно то, что в файле: удалённые аккаунты не воскресают
            for slot, acc in accounts.items():
                if isinstance(acc, dict):
                    config["accounts"][str(slot)] = {**BLANK_ACCOUNT, **acc}
        elif legacy:
            config["accounts"]["1"].update(legacy)  # самый старый формат -> аккаунт 1
        if isinstance(roles, dict):
            for role in ("collector", "sender"):
                if str(roles.get(role)) in config["accounts"]:
                    config["roles"][role] = str(roles[role])
        if isinstance(modes_in, dict):
            config["chat_modes"] = {str(r): m for r, m in modes_in.items() if m in CHAT_MODES}
        else:   # перенос со старых двух списков: источники -> ИСТ, исключения -> БС (БС важнее)
            migrated = {str(r): "src" for r in config.get("chat_source_groups") or []}
            migrated.update({str(r): "bs" for r in config.get("chat_exclude_groups") or []})
            config["chat_modes"] = migrated
    fix_roles(config)
    fix_tabs(config)
    derive_chat_lists(config)
    _cfg_cache.update(stamp=stamp, data=config)
    return copy.deepcopy(config)


def read_processed():
    if not os.path.exists(PROCESSED_FILE):
        return set()
    with open(PROCESSED_FILE, "r", encoding="utf-8") as f:
        return {line.strip().lstrip("@").lower() for line in f if line.strip()}


def append_processed(username):
    with open(PROCESSED_FILE, "a", encoding="utf-8") as f:
        f.write(username.strip().lstrip("@").lower() + "\n")


admin_ids = {int(x) for x in load_config().get("admin_ids", []) if str(x).lstrip("-").isdigit()}

dp = Dispatcher()
router = Router()

login = {}        # uid -> {"slot", "step", "client", "phone", "hash"}
waiting = {}      # uid -> "set:<cmd>" | "account:<slot>" | "tabadd:..." | "tabren:..."
ui_tab = {"id": None}     # какая вкладка сейчас открыта в /chats и /schedule ("*" — все)
run_locks = set()


# ---------------------------------------------------------
# Общие помощники: текст, сообщения, повторы
# ---------------------------------------------------------

def esc(value):
    return html.escape(str(value), quote=False)


def strip_tags(text):
    return html.unescape(re.sub(r"</?[a-z][^>]*>", "", text))


def short(text, n=40):
    text = " ".join(str(text).split())
    return text if len(text) <= n else text[: n - 1] + "…"


async def tg_call(fn, tries=5):
    """Вызов Bot API с повторами: ждёт при лимитах (retry_after) и сетевых сбоях. Прочие ошибки пробрасывает."""
    for attempt in range(tries):
        try:
            return await fn()
        except TelegramRetryAfter as e:
            await asyncio.sleep(float(e.retry_after) + 0.5)
        except (TelegramNetworkError, TelegramServerError, asyncio.TimeoutError, ConnectionError):
            if attempt == tries - 1:
                raise
            await asyncio.sleep(1.5 * (attempt + 1))
    return await fn()


async def notify(message, text, kb=None, reply=False):
    """Отправка с HTML. Ждёт при лимитах и сетевых сбоях, при кривой разметке шлёт простым текстом, не падает.
    reply=True — ответ реплаем на сообщение (так видно, к какому пересланному сообщению относится ответ)."""
    plain = False
    send = message.reply if reply and hasattr(message, "reply") else message.answer
    for _ in range(3):
        try:
            return await tg_call(lambda: send(strip_tags(text) if plain else text,
                                              parse_mode=None if plain else "HTML", reply_markup=kb))
        except Exception as e:
            if "parse entities" in str(e).lower() and not plain:
                plain = True
                continue
            log.warning("notify: %s: %s", type(e).__name__, e)
            return None
    return None


async def edit(msg, text, kb=None):
    try:
        await tg_call(lambda: msg.edit_text(text, parse_mode="HTML", reply_markup=kb))
    except Exception as e:
        low = str(e).lower()
        if "not modified" in low:
            return
        if "parse entities" in low:
            with suppress(Exception):
                await tg_call(lambda: msg.edit_text(strip_tags(text), parse_mode=None, reply_markup=kb))
        else:
            log.warning("edit: %s: %s", type(e).__name__, e)


async def retry(fn, tries=4):
    """Повторяет запрос при временной ошибке Telegram (паузы 2, 4, 6 сек)."""
    for attempt in range(tries):
        try:
            return await fn()
        except TRANSIENT:
            if attempt == tries - 1:
                raise
            await asyncio.sleep(2 * (attempt + 1))


def admin(fn):
    """Только для админов бота + единая обработка ошибок (бот не молчит, если что-то упало)."""
    @wraps(fn)
    async def wrapper(event):
        user = getattr(event, "from_user", None)
        msg = event.message if isinstance(event, CallbackQuery) else event
        if not user or user.id not in admin_ids:
            if isinstance(event, CallbackQuery):
                await event.answer("Нет доступа", show_alert=True)
            else:
                await notify(msg, "Ошибка: Нет доступа")
            return
        try:
            await fn(event)
        except Exception as e:
            log.exception("ошибка в команде")
            await notify(msg, f"Ошибка: <b>Ошибка:</b> {esc(type(e).__name__)}: {esc(e)}")
    return wrapper


def args_of(message):
    return message.text.split()[1:]


def slots_sorted(cfg):
    return sorted(cfg["accounts"], key=int)


def role_mark(cfg, slot):
    if slot == cfg["roles"]["collector"]:
        return " · сборщик"
    if slot == cfg["roles"]["sender"]:
        return " · отправитель"
    return ""


def normalize_phone(value):
    value = re.sub(r"[\s\-()]", "", value)
    return value if re.fullmatch(r"\+[1-9]\d{7,14}", value) else None


def normalize_code(value):
    """Код вводится как ###.## — возвращаем цифры без точки."""
    value = value.strip().replace(" ", "")
    return value.replace(".", "") if re.fullmatch(r"\d{3}\.\d{2}", value) else None


def normalize_ref(token):
    """Чат из ввода: ID, id канала без -100, @юзернейм, ссылка t.me/..., ссылка на сообщение t.me/c/ID/N."""
    t = token.strip().strip(",;")
    t = re.sub(r"^(https?://)?(www\.)?t\.me/", "", t).split("?")[0]
    if re.fullmatch(r"c/\d+(/\d+)?", t):
        t = "-100" + t.split("/")[1]
    if not re.fullmatch(r"-?\d+", t):
        t = t.lstrip("@").split("/")[0]
    elif re.fullmatch(r"\d{9,}", t):
        t = "-100" + t
    return t


def parse_refs(text):
    seen, out = set(), []
    for tok in re.split(r"[\s,;]+", text.strip()):
        ref = normalize_ref(tok)
        if ref and ref not in seen:
            seen.add(ref)
            out.append(ref)
    return out


# ---------------------------------------------------------
# Аккаунты Telegram: сессии, подключение, проверка входа
# ---------------------------------------------------------

def session_file(slot):
    # Совместимость со старыми сессиями: 1 = my_session, 2 = sender_session
    return {"1": "my_session", "2": "sender_session"}.get(slot, f"session_{slot}")


def session_exists(slot):
    return os.path.exists(session_file(slot) + ".session")


def create_client(slot):
    acc = load_config()["accounts"].get(slot)
    api_id = int((acc or {}).get("api_id") or 0)
    api_hash = str((acc or {}).get("api_hash") or "").strip()
    if not api_id or not api_hash:
        raise ValueError(f"Аккаунт {slot}: не заданы API_ID/API_HASH (/account {slot})")
    # connection_retries: Telethon сам переподключается ~40 сек, потом сдаётся — дальше подхватывает watchdog_loop
    return TelegramClient(session_file(slot), api_id, api_hash,
                          connection_retries=20, retry_delay=2, auto_reconnect=True,
                          request_retries=5, timeout=15)


async def is_authorized(slot, quick=False):
    """Рабочая ли сессия аккаунта. quick=True — только наличие файла сессии."""
    if not session_exists(slot):
        return False
    if quick:
        return True
    try:
        return (await get_client(slot)) is not None
    except Exception:
        return False


@asynccontextmanager
async def account_client(slot):
    """Клиент аккаунта из пула (подключение общее, закрывать не нужно)."""
    client = await get_client(slot)
    if client is None:
        raise RuntimeError("не авторизован")
    yield client


async def with_chat_access(ref, job):
    """Пробует аккаунты по очереди (сборщик, отправитель, остальные) и выполняет job(client, entity, slot)
    на первом, у которого есть доступ к чату. Возвращает (slot, результат)."""
    cfg = load_config()
    roles = cfg["roles"]
    order = [roles["collector"], roles["sender"]] + [s for s in slots_sorted(cfg) if s not in roles.values()]
    for slot in order:
        acc = cfg["accounts"].get(slot, {})
        if not session_exists(slot) or not acc.get("api_id") or not acc.get("api_hash"):
            continue
        try:
            client = await get_client(slot)
        except Exception:
            continue                      # аккаунт не подключился — пробуем следующий, а не падаем целиком
        if client is None:
            continue
        try:
            entity = await retry(lambda: resolve_chat(client, ref))
        except FloodWaitError:
            raise
        except (ValueError, RPCError):
            continue                      # у этого аккаунта нет доступа — пробуем следующий
        return slot, await job(client, entity, slot)
    raise RuntimeError("ни один аккаунт не имеет доступа к этому чату")


_dialogs_at = {}


async def load_dialogs(client):
    """Подтянуть список диалогов, чтобы Telethon узнал чаты. Не чаще раза в минуту на клиента и не дольше 2 минут
    (раньше на каждый неизвестный чат читались ВСЕ диалоги без ограничения по времени)."""
    key = id(client)
    if time.time() - _dialogs_at.get(key, 0) < 60:
        return
    _dialogs_at[key] = time.time()
    with suppress(asyncio.TimeoutError):
        await asyncio.wait_for(client.get_dialogs(limit=None), 120)


async def resolve_chat(client, value):
    ref = int(value) if re.fullmatch(r"-?\d+", str(value)) else value
    try:
        return await client.get_entity(ref)
    except ValueError:
        await load_dialogs(client)  # Telethon мог ещё не знать чат
        return await client.get_entity(ref)


# ---------------------------------------------------------
# Статус и отчёты: минимум сообщений
# ---------------------------------------------------------

@asynccontextmanager
async def working(message, text="Работаю…"):
    """Одно временное сообщение на время долгой операции — после неё оно удаляется."""
    msg = await notify(message, text)
    try:
        yield
    finally:
        if msg is not None:
            with suppress(Exception):
                await msg.delete()


class Outbox:
    """Очередь сообщений в чат: каждое уходит отдельным сообщением (1 человек = 1 сообщение),
    с паузой ~1 с, чтобы не упереться в лимиты Telegram, и не тормозит саму рассылку."""

    def __init__(self, message, gap=1.1):
        self.message, self.gap = message, gap
        self.queue = asyncio.Queue()
        self.task = asyncio.create_task(self._worker())

    async def _worker(self):
        while True:
            text = await self.queue.get()
            try:
                await notify(self.message, text)
            except Exception:
                pass
            self.queue.task_done()
            await asyncio.sleep(self.gap)

    def add(self, line):
        self.queue.put_nowait(line)

    async def close(self, timeout=120):
        with suppress(Exception):
            await asyncio.wait_for(self.queue.join(), timeout)
        self.task.cancel()


# ---------------------------------------------------------
# Операции и остановка (/stop)
# ---------------------------------------------------------

class StopRun(BaseException):
    """Операцию попросили остановить (BaseException — чтобы её не поймали обычные except Exception)."""


class Op:
    def __init__(self, name):
        self.name = name
        self.stop = False
        self.task = asyncio.current_task()
        self.timer = None


ops = set()
current_op = ContextVar("current_op", default=None)


def check_stop():
    op = current_op.get()
    if op is not None and op.stop:
        raise StopRun()


async def interruptible_sleep(sec):
    loop = asyncio.get_running_loop()
    end = loop.time() + sec
    while True:
        check_stop()
        left = end - loop.time()
        if left <= 0:
            return
        await asyncio.sleep(min(0.5, left))


def request_stop():
    """Мягкая остановка: операция остановится на ближайшем шаге. Если застряла — через 12 сек обрываем жёстко."""
    loop = asyncio.get_running_loop()
    for op in list(ops):
        op.stop = True
        if op.timer is None and op.task is not None:
            op.timer = loop.call_later(12, op.task.cancel)
    return len(ops)


async def run_op(message, name, fn, extra=None):
    """Выполняет fn() как останавливаемую операцию. extra() — текст с промежуточным итогом при остановке."""
    op = Op(name)
    ops.add(op)
    token = current_op.set(op)
    stopped = False
    try:
        await fn()
    except StopRun:
        stopped = True
    except asyncio.CancelledError:
        if not op.stop:
            raise
        stopped = True
    finally:
        if op.timer is not None:
            op.timer.cancel()
        ops.discard(op)
        current_op.reset(token)
    if stopped:
        tail = extra() if extra else ""
        await notify(message, f"<b>{esc(name)} остановлена</b>" + (f"\n{tail}" if tail else ""))


def operation(name):
    """Декоратор: команда становится останавливаемой операцией."""
    def deco(fn):
        @wraps(fn)
        async def wrapper(message):
            await run_op(message, name, lambda: fn(message))
        return wrapper
    return deco


# ---------------------------------------------------------
# Распознавание ответов в ЛС: согласие / отказ / вопрос / «не пиши»
# ---------------------------------------------------------

# Раскладка EN -> RU (если человек писал не переключив раскладку: «lfdfq» = «давай»)
EN_TO_RU = dict(zip("qwertyuiop[]asdfghjkl;'zxcvbnm,.", "йцукенгшщзхъфывапролджэячсмитьбю"))
# Латинские буквы, похожие на кириллицу (смешанные слова: «дaвай»)
HOMOGLYPHS = {"a": "а", "e": "е", "o": "о", "c": "с", "p": "р", "x": "х", "y": "у",
              "k": "к", "m": "м", "t": "т", "b": "в", "h": "н"}
# Латиница и транслит -> русские слова
LATIN_MAP = {
    "yes": "да", "yep": "да", "yeah": "да", "yea": "да", "yup": "да", "da": "да", "ok": "ок", "okay": "окей",
    "okey": "окей", "sure": "конечно", "go": "го", "goo": "го", "gou": "го", "davai": "давай", "davay": "давай",
    "ladno": "ладно", "hochu": "хочу", "khochu": "хочу", "konechno": "конечно", "pogнали": "погнали",
    "net": "нет", "ne": "не", "no": "нет", "nope": "нет", "nah": "нет", "neа": "неа",
    "hi": "привет", "hello": "привет", "hey": "привет", "yo": "привет", "privet": "привет", "hola": "привет",
    "stop": "стоп", "spam": "спам", "report": "репорт", "block": "блок", "ban": "бан",
    "why": "зачем", "what": "что", "who": "кто", "how": "как", "where": "где",
}


def norm_token(tok):
    tok = tok.lower().replace("ё", "е")
    if tok in LATIN_MAP:
        return norm_token_ru(LATIN_MAP[tok])
    if re.fullmatch(r"[a-z\[\];',.]+", tok):                    # чистая латиница -> пробуем раскладку
        tok = "".join(EN_TO_RU.get(ch, ch) for ch in tok)
    elif re.search(r"[а-я]", tok):                                # смешанные алфавиты -> похожие буквы
        tok = "".join(HOMOGLYPHS.get(ch, ch) for ch in tok)
    return norm_token_ru(tok)


def norm_token_ru(tok):
    tok = re.sub(r"(.)\1+", r"\1", tok)                           # дааа -> да, хачуу -> хачу
    tok = re.sub(r"^(да){2,}$", "да", tok)                        # дада -> да
    tok = re.sub(r"^(не){2,}$", "не", tok)                        # нененене -> не
    return tok


def tokenize(text):
    return [norm_token(t) for t in re.findall(r"[a-zа-яё0-9\[\];',.]+|\+", text.lower().replace("’", "'")) if t.strip(",.;'[]")]


def _ph(phrases):
    return tuple(" ".join(norm_token_ru(t.replace("ё", "е")) for t in p.split()) for p in phrases)


def _words(words):
    return {norm_token_ru(w.replace("ё", "е")) for w in words}


# --- согласие ---
AGREE_WORDS = _words("""да ага агась угу конечно хочу хачу ок окей оке хорошо ладно давай давайте го погнали поехали можно
согласен согласна согласны готов готова жду интересно интересует вперед запросто базара нет бегу иду приду буду плюс +
гоу допустим заинтересован заинтересована""".split())
AGREE_PHRASES = _ph([
    "я хочу", "я хачу", "я в деле", "в деле", "я за", "тоже хочу", "хочу играть", "давай играть", "го играть",
    "го в мафию", "го мафия", "го в игру", "я из анонки", "из анонки", "конечно хочу", "да хочу", "ну да", "да да",
    "ага да", "угу да", "давай ссылку", "скинь ссылку", "кидай ссылку", "кидай", "скидывай", "дай ссылку", "где ссылка",
    "как попасть", "как зайти", "как вступить", "как присоединиться", "куда писать", "куда заходить", "где играть",
    "скинь", "скиньте", "кинь", "киньте", "пришли", "пришлите", "отправь", "отправьте", "покажи", "покажите",
    "присылай", "скинешь", "кинешь", "давай посмотрим", "давайте посмотрим", "скинь посмотрим", "дай посмотреть",
    "можно попробовать", "давай попробуем", "давайте попробуем", "я готов", "я готова", "я согласен", "я согласна",
    "я согласны", "с удовольствием", "с радостью", "почему бы и нет", "почему бы нет", "а почему бы и нет",
])
# «не против», «не откажусь», «нет вопросов» — отрицание, но по смыслу согласие. Проверяется ПЕРВЫМ.
AGREE_OVERRIDE = _ph([
    "не против", "не откажусь", "не откажусь не", "нет вопросов", "не вопрос", "не проблема", "нет проблем",
    "без проблем", "почему бы и нет", "почему бы нет", "а почему бы и нет", "не вижу проблем", "не возражаю",
])

# --- отказ ---
REFUSAL_WORDS = _words("""нет неа не ноу нах нахер нахуй хуй хер хватит харе пас пасс
мимо против отказываюсь отказ забей забейте неинтересно никогда сука""".split())
REFUSAL_PHRASES = _ph([
    "не хочу", "не буду", "не надо", "не нужно", "не интересно", "не интересует", "не хочется", "не люблю",
    "не играю", "не по адресу", "не мое", "нет спасибо", "не спасибо", "спасибо нет", "нет уж", "ни за что",
    "не согласен", "не согласна", "не согласны", "не готов", "не готова", "не могу", "не до этого", "не до игр",
    "я против", "я не буду", "я не хочу", "не трогай", "мне не интересно", "мне это не надо", "мне не надо",
    "мне не нужно", "меня не интересует", "нет желания", "нет времени", "нет интереса", "нет настроения",
    "нет возможности", "не актуально", "уже не актуально", "не пойду", "не приду", "не вариант", "это не для меня",
    "пошел ты", "пошла ты", "иди ты", "иди на", "иди нах", "пошел нах", "пошли вы", "идите нах", "отвали от меня",
    "отстань от меня", "я отказываюсь", "нет не хочу", "нет не надо",
])
# После «не» эти слова означают отказ: «не хочу», «не готов», «не буду»... (ловит и опечатки/формы)
NEG_TARGETS = _words("""хочу хачу буду надо нужно готов готова согласен согласна согласны интересно интересует хочется могу
играю люблю пойду приду актуально нуждаюсь собираюсь планирую""".split())

# --- «не пиши»: молчим и закрываем диалог, чтобы не получить жалобу ---
STOP_WORDS = _words("""спам спамер спамишь стоп блок блокирую заблокирую пожалуюсь репорт бан забаню отпишись отписаться
удали удалите мошенник мошенники развод лохотрон разводилово""".split())
STOP_PHRASES = _ph([
    "не пиши", "не пишите", "не пиши мне", "не пишите мне", "перестань писать", "перестаньте писать", "хватит писать",
    "оставь меня", "оставьте меня", "не пиши больше", "больше не пиши", "больше не пишите", "удали мой номер",
    "я пожалуюсь", "это спам",
])

# --- вопрос ---
QUESTION_WORDS = _words("""зачем почему чего что кто кого куда откуда когда сколько как где какой какая какое какие чем разве
правда серьезно реально подробнее правила объясни поясни расскажи""".split())
QUESTION_STARTERS = _words("""зачем почему что чего кто кого куда откуда когда сколько как где какой какая какое какие чем разве""".split())
QUESTION_PHRASES = _ph([
    "что это", "что за", "что за игра", "что за мафия", "что там", "что там делать", "что делать", "что нужно делать",
    "что надо делать", "как это", "как играть", "как это работает", "в чем суть", "в чем смысл", "в смысле", "а что",
    "а как", "а зачем", "а почему", "кто ты", "ты кто", "кто это", "кто вы", "вы кто", "откуда ты", "откуда знаешь",
    "откуда номер", "это что", "это кто", "ты бот", "вы бот", "это бот", "это реклама", "реклама", "расскажи подробнее",
    "что просто", "а что это", "а как это", "а что там делать", "а что за мафия", "а что просто", "что взамен",
    "что мне за это", "а что мне", "а если", "а можно", "а сколько", "сколько платят", "что за приглашение",
])
# «не знаю», «не понял» — человек не отказывается, а просит пояснить
QUESTION_OVERRIDE = _ph(["не знаю", "не понял", "не поняла", "не понимаю", "не уверен", "не уверена", "сомневаюсь", "хз", "мб"])
# «позже», «потом», «не сейчас» — решения ещё нет: не отвечаем сами, бот только сообщит вам
DELAY_WORDS = _words("позже попозже потом завтра сегодня-потом".split())
DELAY_PHRASES = _ph(["не сейчас", "в другой раз", "как нибудь", "когда нибудь", "на днях", "на неделе", "после работы", "через час"])
AGREE_LEADERS = _words("давай давайте го погнали поехали скинь скиньте кинь киньте пришли пришлите покажи покажите".split())

# --- «откуда у тебя мой контакт?» — отдельный вопрос со своим ответом (/text6) ---
SOURCE_ME = _words("""меня мой мое моя мои моего моей контакт номер ник юз юзернейм акк аккаунт профиль телеграм тг""".split())
SOURCE_VERBS = _words("""знаешь знаете узнал узнала узнали взял взяла взяли нашел нашла нашли вышел вышла вышли достал достала
достали раздобыл раздобыла получил получила получили""".split())
GREETINGS = _words("""привет приветик приветствую здарова здравствуй здравствуйте хай хей ку салют алло але йоу добрый""".split())

AGREE_EMOJI = set("👍👌✅🔥💪🤝😁😊🙂😉❤🥰😍🤩👏🙌✌🤙🆗💯😎😀😃😄➕✔✓☑🆒🫡🫶🙏🤗😇😺😸😻🥳🎉🌟⭐✨💫🚀🏆🥇🎯🤜🤛🤞🫰💚💙💜🧡💛🤍💗💖💕💞💓❣😆😋😜😏😌👊✊🔝⚡🌞☀🤠😻😘😚🥹🙆💃🕺✌")
# «+», «++», «1», «х», «x», «д», «y» и подобные короткие ответы (сравниваются целиком, без пробелов)
AGREE_SYMBOL_WORDS = set("""
+ ++ +++ ++++ +1 +) +- -+ +/- ± 1 11 111 x xx xxx xxxx х хх ххх хххх × ✕ икс иксы плюс плюсик плюсики плюсую плюсы плюс-минус плюсминус плюс/минус
д да дя дэ даа дааа дада дадада yes yep yup yeap yeah yea ye y ya da sure ok okay oke oki okey okk k kk alright fine absolutely definitely def sim oui
ок окей оке окк окэй окай океюшки окейка окейс окей) хорошо ладно добро норм нормас нормально отлично супер класс круто кайф огонь топ имба чётко четко
го gо go letsgo lets-go let'sgo погнали поехали вперёд вперед заходим захожу зайду иду приду буду готов готова готовы согласен согласна согласны
яза базар заметано договорились порукам по-рукам идёт идет сделаем сойдёт сойдет пойдёт пойдет подойдёт подойдет принимается угу ага агась мгм
конечно разумеется естественно безусловно обязательно тактак таккт точно такточно хочу хачу давай давайте
""".split())
REFUSAL_SYMBOL_WORDS = {"-", "--", "---", "минус", "минусую", "н", "no", "nope", "nah", "n"}
REFUSAL_EMOJI = set("👎❌🚫🖕😡🤬😠🙅✋➖✖✗✘❎🙁☹😞🥲")
STOP_EMOJI = set("🛑⛔")
QUESTION_EMOJI = set("❓❔🤔🧐🤨😳🤷")


def _has(padded, phrases):
    return any(f" {p} " in padded for p in phrases)


def is_source_question(toks):
    """«откуда у тебя мой контакт», «как ты меня нашёл», «где взял мой номер»..."""
    if _has(" " + " ".join(toks) + " ", SOURCE_PHRASES):
        return True
    has_me = any(t in SOURCE_ME for t in toks)
    has_verb = any(t in SOURCE_VERBS for t in toks)
    if "откуда" in toks and (has_me or has_verb or "ты" in toks or "вы" in toks):
        return True
    if "как" in toks and has_verb and has_me:
        return True
    if "где" in toks and has_verb and has_me:
        return True
    return False


# --- дополнения к спискам: больше живых формулировок ---
AGREE_WORDS |= _words("""норм нормально отлично супер класс круто кайф прикольно любопытно звучит попробую попробуем
посмотрю гляну зайду присоединюсь""".split())
AGREE_PHRASES += _ph([
    "ну давай", "ладно давай", "давай давай", "хорошо давай", "я не против", "почему нет", "а почему нет",
    "хочу в игру", "запиши меня", "добавь меня", "добавьте меня", "возьми меня", "возьмите меня", "пригласи",
    "пригласите", "приглашай", "приглашайте", "я с вами", "я с тобой", "можно с вами", "в игру",
])
REFUSAL_WORDS |= _words("обойдусь".split())
REFUSAL_PHRASES += _ph([
    "не катит", "не зайдет", "не зашло", "это не мое", "я пас", "не мой формат", "не стоит", "увы нет",
    "к сожалению нет", "к сожалению не", "нет благодарю", "извини не", "извините не", "не надо мне",
])
NEG_TARGETS |= _words("катит зайдет зашло стоит умею".split())
STOP_WORDS |= _words("жалоба жалобу пожаловался надоел надоели надоело прекрати прекратите перестань перестаньте".split())
STOP_PHRASES += _ph(["хватит спамить", "не спамь", "не спамьте", "не звони", "не звоните"])
QUESTION_WORDS |= _words("бесплатно платно подвох условия цена цены".split())
QUESTION_PHRASES += _ph([
    "о чем речь", "о чем это", "о чем", "про что", "про что это", "в чем прикол", "в чем дело", "в чем подвох",
    "где подвох", "что предлагаешь", "что предлагаете", "что за предложение", "какие правила", "какие условия",
    "это бесплатно", "а бесплатно", "сколько стоит", "есть подвох", "что за хрень", "что за ерунда",
])
# «это не развод?», «не спам?» — человек сомневается, а не просит отстать
QUESTION_OVERRIDE += _ph(["это не развод", "не развод", "не лохотрон", "не мошенник", "не мошенники", "это не спам",
                          "не спам", "не обман", "не мошенничество"])

# --- ещё формулировки (раунд 2) ---
LATIN_MAP.update({"fuck": "хуй", "fck": "хуй", "wtf": "хуй", "shit": "говно", "thanks": "спасибо", "thx": "спасибо",
                  "ty": "спасибо", "spasibo": "спасибо", "pls": "пожалуйста", "plz": "пожалуйста"})

AGREE_WORDS |= _words("""ссылку ссылка заинтересовало заинтересовал заинтересовалась обязательно разумеется безусловно
однозначно айда сойдет""".split())
AGREE_PHRASES += _ph([
    "ок го", "го попробуем", "давай попробуем", "ща зайду", "жду ссылку", "пиши ссылку", "присылай ссылку", "а давай",
    "можно ссылку", "было бы интересно", "звучит интересно", "хотелось бы", "я бы поиграл", "я бы поиграла",
    "могу попробовать", "ладно попробую", "окей давай", "да можно", "можно да", "ну можно", "ну ладно", "почему бы",
    "буду играть", "уже иду", "заходи", "давай ссылку", "где играем", "когда играем", "когда игра", "во сколько игра",
    "в какое время игра", "хочу в чат", "хочу к вам", "возьмите в чат", "добавьте в чат", "добавь в чат",
])
AGREE_OVERRIDE += _ph(["базара нет", "не откажусь", "не против поиграть", "нет возражений"])

REFUSAL_PHRASES += _ph([
    "да ну", "да ну нафиг", "ну нафиг", "да нет", "не интересуюсь", "не увлекаюсь", "мне неинтересно", "я не играю",
    "не по теме", "не туда", "ошиблись", "вы ошиблись", "ты ошибся", "ошибся номером", "не тот человек",
    "не туда попали", "не туда написал", "не ко мне", "не для меня", "без меня", "не нуждаюсь", "не требуется",
    "не собираюсь", "не вижу смысла", "смысла нет", "нет смысла", "не вижу интереса", "не мое", "мне это не нужно",
    "мне это неинтересно", "оставь себе", "сам играй", "сами играйте",
])
REFUSAL_WORDS |= _words("неинтересно отказ нафиг не_надо".split())

STOP_WORDS |= _words("""полиция полицию прокуратура прокуратуру суд судом заявление жалуюсь жаловаться заблокировал
заблокировала заблокировать отписка""".split())
STOP_PHRASES += _ph([
    "не пишите мне больше", "удалите мой номер", "забудь меня", "забудьте меня", "удали меня", "удалите меня",
    "отпишите меня", "в бан", "кидаю в спам", "подам жалобу", "напишу жалобу", "иду жаловаться", "в покое",
    "оставь в покое", "оставьте в покое", "забудь мой номер", "забудьте мой номер", "не беспокой", "не беспокойте",
    "не доставай", "не доставайте", "не донимай", "не донимайте", "в черный список", "в чс",
])

QUESTION_WORDS |= _words("че чо шо чем".split())
QUESTION_STARTERS |= _words("че чо шо".split())
QUESTION_PHRASES += _ph([
    "что за группа", "что за чат", "что за канал", "что за сообщество", "что за анонка", "что такое мафия",
    "что такое анонка", "это про что", "про что речь", "а ты кто", "ты вообще кто", "вы вообще кто", "с кем я говорю",
    "с кем говорю", "это вы кто", "кто пишет", "а вы кто", "вы откуда", "зачем тебе это", "что от меня надо",
    "что тебе надо", "что вам нужно", "что вам от меня надо", "чего ты хочешь", "чего вы хотите", "что хочешь",
    "что хотите", "ты по какому вопросу", "по какому поводу", "по какому вопросу", "что ты хочешь", "что именно",
    "какая игра", "какая мафия", "какой формат", "сколько человек", "сколько игроков", "сколько длится", "где проходит",
    "и что", "и че", "че там", "че за", "че это", "шо за", "что за люди", "что за админы", "что за режимы",
    "какие режимы", "какие роли", "а там что", "как у вас", "как там у вас",
])
QUESTION_OVERRIDE += _ph(["хз", "хз хз", "х3", "незнаю", "хм", "хмм", "ну хз", "мб да", "мб", "может быть", "наверное", "посмотрим"])

DELAY_WORDS |= _words("вечером утром выходные выходных занят занята занято днем".split())
DELAY_PHRASES += _ph([
    "сейчас не могу", "не могу сейчас", "я занят", "я занята", "занят сейчас", "потом отвечу", "отвечу позже",
    "напишу позже", "на выходных", "в выходные", "попозже отвечу", "позже отвечу", "подумаю", "я подумаю", "дай подумать",
])

# --- «откуда мой контакт» — больше формулировок ---
SOURCE_PHRASES = _ph([
    "кто дал мой", "кто тебе дал", "кто вам дал", "кто тебе сказал мой", "кто тебе слил", "кто слил", "кто вам слил",
    "в каком чате", "из какого чата", "из какой группы", "в какой группе", "из какого ты чата", "как вы получили мой",
    "как у вас мой", "почему у тебя мой", "почему у вас мой", "зачем тебе мой номер", "зачем вам мой", "откуда инфа",
    "откуда информация", "откуда данные", "откуда мои данные", "где взял мои", "где взяли мои", "где взяла мои",
    "как нашли меня", "как нашел меня", "как нашла меня", "как ты меня нашел", "как вы меня нашли", "кто дал контакт",
    "кто дал мой контакт", "кто дал мой ник", "кто дал мой юз", "откуда у вас", "откуда у тебя", "откуда у вас мой",
])
GREETINGS |= _words("доброе доброго здрасте здрасьте хэй хелло хеллоу приветики".split())
AGREE_EMOJI |= set("🥳🎉🤗😋😌🤭")
REFUSAL_EMOJI |= set("🙄😒😑😤🤦💩🤮🤡")
STOP_EMOJI |= set("🚷📵🔇")
QUESTION_EMOJI |= set("♂♀")

FILLERS = _words("а ну так слушай слышь эй блин короче типа вот и же".split())
ACK_WORDS = _words("спасибо благодарю понял поняла понятно ясно ясненько принял принято спс пасиб пасибо мерси благодарствую сенкс".split())
ACK_PAIR = ACK_WORDS | _words("ок окей оке хорошо ладно угу".split())

# слабые «да/ок/норм» — согласие, только если в сообщении почти ничего больше нет («да», «ну да», «ок норм»).
AGREE_WEAK = _words("""да ага агась угу ок окей оке норм нормально хорошо ладно можно интересно допустим плюс + конечно
отлично супер класс круто кайф прикольно любопытно звучит""".split())
AGREE_STRONG = AGREE_WORDS - AGREE_WEAK

# --- мат и оскорбления: на них не отвечаем и не уговариваем, диалог закрывается ---
CURSE_PREFIX = ("хуй", "хуе", "хуя", "хуи", "хую", "пизд", "пезд", "бля", "мудак", "мудил", "мудо", "долбо", "дебил",
                "идиот", "урод", "тупой", "тупая", "тупое", "пидор", "пидр", "пидар", "гандон", "говн", "залуп", "чмо",
                "ублюд", "шлюх", "мраз", "тварь", "твари", "падл", "гнид", "дерьм", "жоп", "заеб", "отъеб", "сука",
                "суки", "суку", "сучк", "сучар", "нахуй", "нахер", "нахрен", "нафиг", "нафик", "похуй", "похер")
CURSE_EXACT = {"нах", "хер", "хрен", "бл", "сук"}
DIRECTED = {"нах", "нахуй", "нахер", "нахрен", "нафиг", "нафик", "хуй", "хер", "хрен", "похуй", "похер"}
GO_AWAY = {"иди", "идите", "пошел", "пошла", "пошли", "катись", "катитесь"}


# «отстань», «отвали» — просьба не писать: не уговариваем, диалог закрывается
STOP_WORDS |= _words("отстань отстаньте отвали отвалите".split())
# двусмысленное: сами не отвечаем, сообщаем админу
AMBIG_PHRASES = _ph(["да ладно", "да ладно тебе", "да ты что", "не может быть", "ну не знаю", "ну такое"])


def is_curse(tok):
    return tok in CURSE_EXACT or tok.startswith(CURSE_PREFIX) or re.match(r"^еб[аулнеиыот]", tok) is not None


def classify_clause(toks):
    if not toks:
        return None
    padded = " " + " ".join(toks) + " "
    core = list(toks)
    while core and core[0] in FILLERS:   # «а давай», «ну да», «слушай, а что это» — вводные слова не считаем
        core.pop(0)
    if not core:
        return None
    n = len(core)

    if _has(padded, AMBIG_PHRASES):
        return None
    if _has(padded, AGREE_OVERRIDE):
        return "agreement"

    # мат: «Да ебанный рот», «А ты нахер пойти не хочешь?» — не согласие и не повод уговаривать
    if any(is_curse(t) for t in toks):
        strong = any(t in AGREE_STRONG for t in core)
        hostile = (any(t in DIRECTED or t in GO_AWAY or t in ("не", "нет") for t in toks)
                   or _has(padded, REFUSAL_PHRASES))
        return "agreement" if (strong and not hostile) else "stop"

    if _has(padded, QUESTION_OVERRIDE):
        return "question"
    if any(t in STOP_WORDS for t in toks) or _has(padded, STOP_PHRASES):
        return "stop"

    # отказ: фразы, «не + хочу/готов/буду...», короткие «нет/не/неа»
    if _has(padded, REFUSAL_PHRASES):
        return "refusal"
    if any(t == "не" and i + 1 < len(toks) and toks[i + 1] in NEG_TARGETS
           for i, t in enumerate(toks)):
        return "refusal"
    if n <= 3 and any(t in REFUSAL_WORDS for t in core):
        return "refusal"

    # вопрос / интерес
    if is_source_question(toks):
        return "source"
    if core[0] in AGREE_LEADERS:             # «давай посмотрим что там» — начало с согласия важнее
        return "agreement"
    if _has(padded, QUESTION_PHRASES):
        return "question"
    if _has(padded, AGREE_PHRASES):          # «как попасть», «где играть» — это интерес, а не вопрос
        return "agreement"
    if n <= 7 and core[0] in QUESTION_STARTERS:
        return "question"
    if n == 1 and core[0] in QUESTION_WORDS:
        return "question"

    # «спасибо», «ок понял» — вежливое подтверждение
    if n <= 3 and all(t in ACK_PAIR for t in core) and any(t in ACK_WORDS for t in core):
        return "ack"

    # согласие: сильные слова («хочу», «давай», «го») — почти всегда; слабые («да», «ок») — только в коротких репликах
    if n <= 5 and any(t in AGREE_STRONG for t in core):
        return "agreement"
    if n <= 2 and any(t in AGREE_WEAK for t in core):
        return "agreement"
    if n <= 4 and any(t in AGREE_WEAK for t in core) and all(t in AGREE_WEAK or t in AGREE_STRONG or t in FILLERS for t in core):
        return "agreement"

    # просто «привет» и всё непонятное — сами не отвечаем, пусть решит админ
    return None


def detect_trigger(text):
    """'agreement' | 'refusal' | 'question' | 'source' | 'stop' | 'ack' | None.
    Сообщение режется на части по знакам препинания; побеждает последняя решающая часть
    («не знаю, давай» -> согласие, «давай, но нет» -> отказ). «stop» важнее всего,
    «ack» («спасибо») — только если ничего другого в сообщении нет."""
    raw = (text or "").strip()
    if not raw:
        return None
    compact = re.sub(r"[\s\u200d\ufe0f\U0001F3FB-\U0001F3FF]", "", raw)
    low = compact.lower()
    bare = re.sub(r"[.,!;:\"'«»()\[\]*~_…]+", "", low)             # «x)», «ок!!», «да...» — знаки не мешают; «?» не трогаем
    forms = {bare, re.sub(r"(.)\1{2,}", r"\1\1", bare), re.sub(r"(.)\1+", r"\1", bare)}   # «дааааа», «ооооок»
    if forms & AGREE_SYMBOL_WORDS:
        return "agreement"
    if forms & REFUSAL_SYMBOL_WORDS:
        return "refusal"
    if compact and all(ch in AGREE_EMOJI or ch in "+±xх×✕" for ch in low):   # любая смесь смайлов, «+», «x»
        return "agreement"
    if compact and all(ch in STOP_EMOJI for ch in compact):
        return "stop"
    if compact and all(ch in REFUSAL_EMOJI or ch == "-" for ch in compact):
        return "refusal"
    if compact and all(ch in QUESTION_EMOJI or ch == "?" for ch in compact):
        return "question"

    lowered = raw.lower()
    clauses = re.split(r"[.,!?;:\n]+|\s[-—–]\s|\sно\s", lowered)
    all_tokens = tokenize(lowered)
    padded_all = " " + " ".join(all_tokens) + " "
    if len(all_tokens) > 30:  # длинное сообщение — это разговор, а не ответ; реагируем только на «не пиши»
        return "stop" if (any(t in STOP_WORDS for t in all_tokens) or _has(padded_all, STOP_PHRASES)) else None

    result, ack = None, False
    for clause in clauses:
        kind = classify_clause(tokenize(clause))
        if kind == "stop":
            return "stop"
        if kind == "ack":
            ack = True
        elif kind:
            result = kind
    if result in ("agreement", "refusal") and (any(t in DELAY_WORDS for t in all_tokens) or _has(padded_all, DELAY_PHRASES)):
        return None   # «ладно, потом» / «давай позже» — решения нет, пусть решит человек
    if result is None and ack:
        return "ack"
    if result is None and "?" in raw and len(all_tokens) <= 12:
        result = "question"   # короткая реплика с вопросительным знаком
    return result


detect_trigger = lru_cache(maxsize=4096)(detect_trigger)   # одинаковые реплики («да», «нет») разбираются один раз


# Первое сообщение от человека, которому бот не писал (например «я из анонки»)
OPENER_WORDS = _words("го гоу мафия мафа".split())
OPENER_PHRASES = _ph(["по поводу мафии", "по поводу игры", "по поводу анонки", "насчет мафии", "насчет игры",
                      "хочу в анонку", "возьмите в игру", "возьмите в мафию", "возьми в игру", "я на мафию", "я на игру",
                      "мафия когда", "когда мафия", "где мафия", "где играем", "го на мафию", "го на игру", "го мафка",
                      "я по мафии", "я по объявлению", "по объявлению", "я по рекламе", "я на анонку", "я в мафию",
                      "я из анонки", "из анонки", "анонка", "го мафия", "го в мафию", "го играть", "го в игру",
                      "го в мафу", "го мафу", "го маф", "хочу в мафию", "хочу играть в мафию"])


def is_opener(text):
    toks = tokenize(text)
    if not toks or len(toks) > 6:
        return False
    if any(t in ("не", "нет") or is_curse(t) for t in toks):   # «не хочу в мафию» — это не приглашение
        return False
    padded = " " + " ".join(toks) + " "
    return _has(padded, OPENER_PHRASES) or (len(toks) == 1 and toks[0] in OPENER_WORDS)


# ---------------------------------------------------------
# Пул аккаунтов: все авторизованные аккаунты подключены постоянно и слушают ЛС
# ---------------------------------------------------------

pool = {}                    # slot -> подключённый TelegramClient
dm_states = {}               # "slot:user_id" -> text1 | text4 | text5 | text5x2 | text6 | text6x2 | done | manual
dm_meta = {}                 # "slot:user_id" -> {"chat", "ref", "name"} — откуда взяли человека
reply_map = {}               # "chat_id:message_id" уведомления -> "slot:user_id" (ответ из бота реплаем)
acc_info = {}                # slot -> {"id", "name", "username", "phone"} (кто это за аккаунт)
spam_state = {}              # slot -> результат проверки @SpamBot
chat_name_cache = {}         # ref чата -> название (для красивых списков)
recent_replies = {}          # (chat_id, hash текста) -> время: защита от дубля одного и того же текста
bot_ref = {"bot": None}
seen_msgs = {}               # "slot:chat:msg" -> ts — какие входящие уже обработаны (нет дублей после catch_up/перезапуска)
dead_slots = set()           # аккаунты с «мёртвой» сессией
dead_count = {}              # slot -> сколько проверок подряд сессия не авторизована (после DEAD_CONFIRMS аккаунт удаляется)
DEAD_CONFIRMS = 5            # ~2,5 мин подряд «не авторизован» = вышли из аккаунта
warned = {}                  # ключ предупреждения -> время (чтобы не спамить)
bg_tasks = set()


def spawn(coro):
    """Фоновая задача со ссылкой (иначе сборщик мусора может её убить)."""
    t = asyncio.create_task(coro)
    bg_tasks.add(t)
    t.add_done_callback(bg_tasks.discard)
    return t

TRIGGER_LABELS = {"agreement": "согласие", "refusal": "отказ", "question": "вопрос",
                  "source": "«откуда контакт?»", "stop": "просит не писать"}


_save_pending = {}
_save_timer = {"h": None}


def load_json(path, default):
    pending = _save_pending.get(path)          # ещё не записанные изменения важнее файла
    if pending is not None and isinstance(pending, type(default)):
        return pending
    try:
        with open(path, "r", encoding="utf-8") as f:
            data = json.load(f)
        return data if isinstance(data, type(default)) else default
    except (OSError, json.JSONDecodeError):
        return default


def _write_json(path, data):
    tmp = path + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        json.dump(data, f, ensure_ascii=False)
    os.replace(tmp, path)


def flush_saves():
    _save_timer["h"] = None
    for path in list(_save_pending):
        data = _save_pending.pop(path)
        try:
            _write_json(path, data)
        except Exception:
            log.exception("не удалось записать %s", path)


def save_json(path, data):
    """Запись откладывается на ~0.7 с: серия изменений = одна запись на диск, цикл событий не тормозит
    (раньше каждое изменение состояния целиком переписывало файл прямо в обработчике)."""
    _save_pending[path] = data
    if _save_timer["h"] is not None:
        return
    try:
        loop = asyncio.get_running_loop()
    except RuntimeError:
        flush_saves()
        return
    _save_timer["h"] = loop.call_later(0.7, flush_saves)


def load_state():
    global dm_states, dm_meta, reply_map, acc_info, spam_state, chat_name_cache, seen_msgs
    dm_states = load_json(DM_STATES_FILE, {})
    dm_meta = load_json(DM_META_FILE, {})
    reply_map = load_json(REPLY_MAP_FILE, {})
    acc_info = load_json(ACC_INFO_FILE, {})
    spam_state = load_json(SPAM_FILE, {})
    chat_name_cache = load_json(CHAT_NAMES_FILE, {})
    seen_msgs = load_json(SEEN_FILE, {})
    rebuild_dm_index()


def remember_chat(ref, name):
    if name and chat_name_cache.get(str(ref)) != name:
        chat_name_cache[str(ref)] = name
        save_json(CHAT_NAMES_FILE, chat_name_cache)


# ---- кто есть кто: понятные подписи аккаунтов ----

def title(slot):
    """Подпись аккаунта для сообщений: «Акк 6 · Иван (@ivan)». Уже экранирована для HTML."""
    info = acc_info.get(slot) or {}
    bits = []
    if info.get("name"):
        bits.append(esc(info["name"]))
    if info.get("username"):
        bits.append("@" + esc(info["username"]))
    if not bits:
        phone = (load_config()["accounts"].get(slot) or {}).get("phone")
        if phone:
            bits.append(esc(phone))
    return f"Акк {slot}" + (" · " + " ".join(bits) if bits else "")


# ---- состояния диалогов ----

dm_by_uid = {}        # uid -> {slot: state} — быстрый поиск по человеку (раньше каждый раз перебирался весь словарь)
dm_locks = {}         # (slot, uid) -> Lock: сообщения одного человека обрабатываются по очереди, а не теряются


def _split_key(k):
    slot, _, uid = k.rpartition(":")      # "slot:uid" -> (slot, uid); старый формат "uid" -> ("?", uid)
    return slot or "?", uid


def rebuild_dm_index():
    dm_by_uid.clear()
    for k, v in dm_states.items():
        slot, uid = _split_key(k)
        dm_by_uid.setdefault(uid, {})[slot] = v


def dm_lock(slot, uid):
    key = (str(slot), uid)
    lock = dm_locks.get(key)
    if lock is None:
        if len(dm_locks) > 2000:
            for k in [k for k, lk in dm_locks.items() if not lk.locked()]:
                dm_locks.pop(k, None)
        lock = dm_locks[key] = asyncio.Lock()
    return lock


def mark_seen(key):
    """True — сообщение новое; False — уже обрабатывали (повторная доставка после catch_up или перезапуска)."""
    if key in seen_msgs:
        return False
    seen_msgs[key] = int(time.time())
    while len(seen_msgs) > 3000:
        seen_msgs.pop(next(iter(seen_msgs)))
    save_json(SEEN_FILE, seen_msgs)
    return True


# старые записи (без номера аккаунта) тоже учитываются
def dm_get(slot, user_id):
    return dm_states.get(f"{slot}:{user_id}") or dm_states.get(str(user_id))


def set_dm_state(slot, user_id, state):
    dm_states[f"{slot}:{user_id}"] = state
    dm_by_uid.setdefault(str(user_id), {})[str(slot)] = state
    save_json(DM_STATES_FILE, dm_states)


def _drop_dm_state(slot, user_id):
    dm_states.pop(f"{slot}:{user_id}", None)
    row = dm_by_uid.get(str(user_id))
    if row is not None:
        row.pop(str(slot), None)
        if not row:
            dm_by_uid.pop(str(user_id), None)


def unset_dm_state(slot, user_id):
    _drop_dm_state(slot, user_id)
    dm_meta.pop(f"{slot}:{user_id}", None)
    save_json(DM_STATES_FILE, dm_states)
    save_json(DM_META_FILE, dm_meta)


def restore_dm_state(slot, user_id, prev):
    """Вернуть прежнее состояние диалога (если ответ не удалось доставить)."""
    if prev:
        set_dm_state(slot, user_id, prev)
    else:
        _drop_dm_state(slot, user_id)
        save_json(DM_STATES_FILE, dm_states)


def set_dm_meta(slot, user_id, meta):
    dm_meta[f"{slot}:{user_id}"] = meta
    save_json(DM_META_FILE, dm_meta)


def dm_meta_get(slot, user_id):
    return dm_meta.get(f"{slot}:{user_id}") or {}


def dm_any(user_id):
    """Состояния диалога этого человека по всем аккаунтам: [(slot, state)]."""
    return list(dm_by_uid.get(str(user_id), {}).items())


def messaged_ids():
    return {int(u) for u in dm_by_uid if u.lstrip("-").isdigit()}


def remove_processed(username):
    name = username.strip().lstrip("@").lower()
    with suppress(Exception):
        lines = [ln for ln in open(PROCESSED_FILE, "r", encoding="utf-8").read().splitlines() if ln.strip().lstrip("@").lower() != name]
        with open(PROCESSED_FILE, "w", encoding="utf-8") as f:
            f.write("".join(ln + "\n" for ln in lines))


def fmt_text(text, meta=None, user=None):
    """Подстановки в текстах: {chat} — чат, где нашли человека; {name} — его имя."""
    meta = meta or {}
    first = (getattr(user, "first_name", None) or meta.get("name") or "").strip()
    return (str(text or "").replace("{chat}", meta.get("chat") or "одном из чатов").replace("{name}", first)).strip()


# ---- общение с админом: сообщаем только о непонятном, ответ — реплаем ----

def trim_reply_map():
    while len(reply_map) > 1000:
        reply_map.pop(next(iter(reply_map)))
    save_json(REPLY_MAP_FILE, reply_map)


async def notify_admins(text, kb=None, key=None):
    """Сообщить админам бота о событии в ЛС. key=(slot, uid) — чтобы можно было ответить реплаем.
    Ждёт при лимитах Telegram и повторяет при сетевых сбоях (раньше уведомление просто терялось)."""
    bot = bot_ref["bot"]
    if bot is None:
        return
    for aid in admin_ids:
        sent = None
        for plain in (False, True):
            try:
                sent = await tg_call(lambda: bot.send_message(
                    aid, strip_tags(text) if plain else text,
                    parse_mode=None if plain else "HTML", reply_markup=kb))
                break
            except Exception as e:
                if not plain and "parse entities" in str(e).lower():
                    continue
                log.warning("notify_admins %s: %s: %s", aid, type(e).__name__, e)
                break
        if sent is None:
            continue
        if key is not None and getattr(sent, "message_id", None):
            reply_map[f"{aid}:{sent.message_id}"] = f"{key[0]}:{key[1]}"
    if key is not None:
        trim_reply_map()


async def warn_once(key, text, every=3600):
    """Предупреждение админам — не чаще раза в `every` секунд."""
    if time.time() - warned.get(key, 0) > every:
        warned[key] = time.time()
        await notify_admins(text)


async def dm_send(slot, user_id, text):
    """Отправить сообщение человеку с нужного аккаунта (из бота: кнопки, ответы)."""
    client = await get_client(slot)
    if client is None:
        raise RuntimeError(f"{title(slot)} не авторизован")
    peer = await client.get_input_entity(int(user_id))
    await client.send_message(peer, text)


# ---- ответы в ЛС ----

async def human_pause(event, lo=1.5, hi=4.0):
    """Пауза с «печатает…», как у живого человека."""
    delay = random.uniform(lo, hi)
    try:
        async with event.client.action(event.chat_id, "typing"):
            await asyncio.sleep(delay)
    except Exception:
        await asyncio.sleep(delay)


async def reply_text(event, text, meta=None, user=None):
    """-> 'ok' | 'dup' (такой же текст уже уходил) | 'empty' | 'error'. При лимитах и сбоях связи повторяет отправку."""
    text = fmt_text(text, meta, user)
    if not text:
        return "empty"
    now = time.time()
    if len(recent_replies) > 2000:
        for k in [k for k, t in recent_replies.items() if now - t > 600]:
            recent_replies.pop(k, None)
    # защита от дубля: тот же текст тому же человеку не чаще раза в 10 минут
    key = (event.chat_id, hash(text))
    if now - recent_replies.get(key, 0) < 600:
        return "dup"
    recent_replies[key] = now
    await human_pause(event)
    for attempt in range(3):
        try:
            await event.respond(text)
            return "ok"
        except FloodWaitError as e:
            if e.seconds > 90 or attempt == 2:
                break
            await asyncio.sleep(e.seconds + 1)
        except TRANSIENT:
            await asyncio.sleep(2 * (attempt + 1))
        except Exception:
            log.exception("не удалось ответить в ЛС")
            break
    recent_replies.pop(key, None)
    return "error"


def ladder_count(state, base):
    """Сколько раз уже отвечали на этот тип реплик: text5 -> 1, text5x2 -> 2 ..."""
    if state == base:
        return 1
    m = re.fullmatch(base + r"x(\d+)", state or "")
    return int(m.group(1)) if m else 0


def ladder_state(base, k):
    return base if k <= 1 else f"{base}x{k}"


async def handle_dm(event, cfg, slot, user, state, trigger, enabled):
    """Сценарий ответов. Состояние обновляется ДО отправки (чтобы не было дублей), а если отправка не удалась —
    возвращается обратно (чтобы вариант текста не «сгорал» зря).
    Отказ и вопрос: на каждое следующее сообщение уходит следующий вариант текста (уговариваем по очереди).
    Согласие: бот проверяет, что ссылка из /text2 не истекла, отправляет её и сообщает вам, что человек, возможно, зайдёт.
    Возвращает (заметка, нужно_ли_сообщить_админу): сообщаем только если бот не смог ответить сам."""
    uid = user.id
    meta = dm_meta_get(slot, uid)
    prev = None if state == "new" else state
    who = f"@{user.username}" if getattr(user, "username", None) else (getattr(user, "first_name", None) or "без имени")
    if trigger == "stop":
        set_dm_state(slot, uid, "done")
        return "", False
    if not enabled:
        return "автоответы выключены", True

    async def ladder(base, key, fallback_key=None):
        """Следующий вариант текста -> 'ok' | 'over' (варианты кончились) | 'dup' | 'empty' | 'error'."""
        variants = list(cfg.get(key) or (cfg.get(fallback_key) if fallback_key else None) or [])
        k = ladder_count(state, base) + 1
        if k > len(variants):
            return "over"
        set_dm_state(slot, uid, ladder_state(base, k))
        res = await reply_text(event, variants[k - 1], meta, user)
        if res == "error":
            restore_dm_state(slot, uid, prev)
        return res

    def not_sent(res, what):
        if res == "error":
            return "не удалось отправить ответ (сбой связи или лимиты Telegram)", True
        return f"{what} пуст или это дубль", True

    if trigger == "refusal":
        res = await ladder("text4", "texts_refusal")
        if res == "over":             # уговорили сколько могли — закрываем диалог молча
            set_dm_state(slot, uid, "done")
            return "", False
        return ("", False) if res == "ok" else not_sent(res, "/text3")
    if trigger == "question":
        res = await ladder("text5", "texts_question")
        if res == "over":
            return "вопросов больше, чем вариантов в /text4", True
        return ("", False) if res == "ok" else not_sent(res, "/text4")
    if trigger == "source":
        res = await ladder("text6", "texts_source", "texts_question")
        if res == "over":
            return "повторно спрашивает про контакт", True
        return ("", False) if res == "ok" else not_sent(res, "/text5")

    # --- согласие: отправляем ссылку из /text2 (если она ещё действует) ---
    if state == "link":                       # ссылку уже выдавали — повторять не нужно
        return "", False
    link_txt = link_text_of(cfg)
    if not link_txt:
        return "согласился, но текст со ссылкой не задан (/text2)", True
    async def over_limit():
        """Суточный лимит ссылок исчерпан: вместо ссылки уходит текст из /text6."""
        if state == "limited":                # сегодня уже сообщали, что мест нет — не спамим
            return "", False
        lim_txt = limit_text_of(cfg)
        if not lim_txt:
            return f"лимит ссылок на сегодня ({day_limit(cfg)}) исчерпан, а текст для таких людей не задан (/text6)", True
        set_dm_state(slot, uid, "limited")
        r = await reply_text(event, lim_txt, meta, user)
        if r == "ok":
            log_event("limit", slot, uid, name=meta.get("name") or getattr(user, "username", None))
            return "", False
        restore_dm_state(slot, uid, prev)
        return not_sent(r, "/text6")

    if day_is_full(cfg, uid):                 # дёшево проверяем до сетевой проверки ссылки
        return await over_limit()
    status, _name = await check_invite(event.client, link_txt)
    if status == "expired":
        return "Внимание: согласился, но ссылка в /text2 истекла — обновите её и ответьте человеку", True
    if not day_reserve(cfg, uid):             # пока проверяли ссылку, последнее место мог занять другой
        return await over_limit()
    set_dm_state(slot, uid, "link")
    res = await reply_text(event, link_txt, meta, user)
    if res == "ok":
        log_event("link", slot, uid, name=meta.get("name") or getattr(user, "username", None))
        lines = [f"<b>ССЫЛКА ОТПРАВЛЕНА</b> — возможно, человек зайдёт",
                 LINE,
                 f"{esc(who)} · <code>{uid}</code>",
                 f"{title(slot)}",
                 f"Ссылок сегодня: <b>{day_line(cfg)}</b>"]
        if meta.get("chat"):
            lines.append(f"Из чата: {esc(meta['chat'])}" + (f" (<code>{meta['ref']}</code>)" if meta.get("ref") else ""))
        await notify_admins("\n".join(lines), key=(slot, uid))
        if day_limit(cfg) and day_used() >= day_limit(cfg):
            await notify_admins(f"<b>ЛИМИТ НА СЕГОДНЯ НАБРАН</b> ({day_used()} из {day_limit(cfg)})\n"
                                "Остальным, кто согласится, бот отправит текст из /text6.\n"
                                "Изменить лимит: /daylimit · сбросить счётчик: /dayreset")
        return "", False
    day_release(uid)                           # не отправилось — место возвращаем
    restore_dm_state(slot, uid, prev)
    return not_sent(res, "/text2")


def media_kind(event):
    m = getattr(event, "message", None)
    if m is None:
        return "вложение"
    for attr, name in (("photo", "фото"), ("voice", "голосовое"), ("video", "видео"), ("sticker", "стикер"),
                       ("audio", "аудио"), ("document", "файл")):
        if getattr(m, attr, None):
            return name
    return "вложение"


def has_media(event):
    """Фото, стикер, голосовое, файл... (ссылки с превью не считаются)."""
    m = getattr(event, "message", None)
    return type(getattr(m, "media", None)).__name__ in ("MessageMediaPhoto", "MessageMediaDocument")


async def forward_media(event, header):
    """Присылает админам само вложение (скрин, стикер, голосовое, файл) — на него можно ответить реплаем."""
    bot = bot_ref["bot"]
    if bot is None:
        return
    m = event.message
    f = getattr(m, "file", None)
    data = None
    if (getattr(f, "size", 0) or 0) <= 20 * 1024 * 1024:
        with suppress(Exception):
            data = await m.download_media(file=bytes)
    sent_to = []
    for aid in admin_ids:
        with suppress(Exception):
            sent = await bot.send_message(aid, header + ("" if data else "\n<i>не удалось скачать вложение</i>"), parse_mode="HTML")
            sent_to.append((aid, sent.message_id))
    if not data:
        return sent_to
    mime = (getattr(f, "mime_type", "") or "").lower()
    name = getattr(f, "name", None) or "file" + (getattr(f, "ext", "") or "")
    if m.photo:
        kind = "photo"
    elif m.sticker:
        kind, name = ("sticker", "sticker.webp") if mime == "image/webp" else ("document", name)
    elif m.voice:
        kind, name = "voice", "voice.ogg"
    elif m.video_note:
        kind = "video_note"
    elif m.video and not m.gif:
        kind = "video"
    elif m.audio:
        kind = "audio"
    else:
        kind = "document"
    senders = {"photo": bot.send_photo, "sticker": bot.send_sticker, "voice": bot.send_voice, "video_note": bot.send_video_note,
               "video": bot.send_video, "audio": bot.send_audio, "document": bot.send_document}
    for aid, _mid in list(sent_to):
        file = BufferedInputFile(data, filename=name)
        try:
            sent = await senders[kind](aid, file)
        except Exception:   # например, у админа закрыты голосовые — шлём файлом
            try:
                sent = await bot.send_document(aid, BufferedInputFile(data, filename=name))
            except Exception:
                continue
        sent_to.append((aid, sent.message_id))
    return sent_to


async def process_dm(event, slot, user):
    """Разбор одного входящего ЛС. Вызывается под замком (slot, человек): сообщения идут по очереди, состояние читается свежим."""
    text = (event.raw_text or "").strip()
    state = dm_get(slot, user.id)
    if state:
        mark_replied(slot, user.id)       # человек ответил — диалог не будет удалён как «без ответа»
    cfg = load_config()
    _m = dm_meta_get(slot, user.id) or {}
    _kw = dict(name=_m.get("name") or getattr(user, "username", None), chat=_m.get("chat"), ref=_m.get("ref"))
    if state and has_media(event):
        log_event("in", slot, user.id, x="media", **_kw)
    elif state and text:
        _x = detect_trigger(text) or ("manual" if state == "manual" else "unclear")
        log_event("in", slot, user.id, x=("closed" if state == "done" and _x == "unclear" else _x), **_kw)
    elif not state and text and is_opener(text):
        log_event("in", slot, user.id, x="agreement", name=getattr(user, "username", None))
    who = f"@{user.username}" if getattr(user, "username", None) else (getattr(user, "first_name", None) or "без имени")

    async def tell(body, note):
        await notify_admins(f"<b>ВХОДЯЩЕЕ СООБЩЕНИЕ</b>\n{LINE}\n{esc(who)} · <code>{user.id}</code>\n"
                            f"{title(slot)}\n\n{body}\n{LINE}\n{note}", key=(slot, user.id))

    if state and has_media(event):    # скрины, стикеры, голосовые — присылаем самим файлом (даже если диалог закрыт)
        header = f"<b>{esc(who)}</b> · <code>{user.id}</code>\n{title(slot)}\n{media_kind(event)}"
        if text:
            header += f"\n«{esc(text[:1000])}»"
        sent_to = await forward_media(event, header + "\n<i>ответьте реплаем</i>")
        for aid, mid in sent_to or []:
            reply_map[f"{aid}:{mid}"] = f"{slot}:{user.id}"
        trim_reply_map()
        return
    if state == "done" or not text:      # диалог закрыт — молчим
        return
    body = f"«{esc(text[:3000])}»"
    if state == "manual":                # вы ведёте диалог сами — пересылаем всё
        await tell(body, "<i>вы ведёте диалог</i>")
        return

    # знакомому — полный сценарий, новому — только «го», «я из анонки» и подобное
    trigger = detect_trigger(text) if state else ("agreement" if is_opener(text) else None)
    if trigger is None:
        if state:
            await tell(body, "<i>смысл не понял — ответьте реплаем</i>")
        return
    if trigger == "ack":
        return

    sent_ts = event.date.timestamp() if getattr(event, "date", None) else time.time()
    age = time.time() - sent_ts
    if age > STALE_SEC and trigger != "stop":     # бот был офлайн: отвечать на старое сообщение автоматом странно
        await tell(body, f"<i>сообщение пришло {fmt_left(age)} назад — автоответ пропущен, ответьте реплаем</i>")
        return

    with suppress(Exception):
        await event.mark_read()
    note, forward = await handle_dm(event, cfg, slot, user, state or "new", trigger, cfg.get("dm_reply_enabled", True))
    if forward:
        await tell(body, f"{TRIGGER_LABELS[trigger]} · <i>{esc(note)} — ответьте реплаем</i>")


async def on_private_message(event, slot):
    """Входящее ЛС на любой подключённый аккаунт.
    Админу уходит только то, что бот не понял или на что не может ответить сам. Всё остальное — молча.
    Ошибки больше не глотаются: пишутся в bot.log и (не чаще раза в 10 минут) приходят вам."""
    try:
        if not event.is_private or event.out:
            return
        if not mark_seen(f"{slot}:{event.chat_id}:{event.id}"):
            return
        user = await event.get_sender()
        if user is None or getattr(user, "bot", False) or user.id in own_ids():
            return
        async with dm_lock(slot, user.id):
            await process_dm(event, slot, user)
    except Exception as e:
        log.exception("ошибка обработки ЛС (акк %s)", slot)
        with suppress(Exception):
            await warn_once("dm_error", f"Внимание: Ошибка обработки ЛС ({title(slot)}): {esc(type(e).__name__)}: {esc(e)}", 600)


def make_dm_handler(slot):
    async def handler(event):
        await on_private_message(event, slot)
    return handler


# ---- подключения ----

slot_locks = {}


def slot_lock(slot):
    """Свой замок на каждый аккаунт: зависший аккаунт больше не блокирует остальные (раньше замок был один общий)."""
    lock = slot_locks.get(slot)
    if lock is None:
        lock = slot_locks[slot] = asyncio.Lock()
    return lock


def login_slots():
    return {st["slot"] for st in login.values()}


async def _drop(slot):
    client = pool.pop(slot, None)
    if client is not None:
        with suppress(Exception):
            await asyncio.wait_for(client.disconnect(), 15)


async def _catch_up(client):
    """Догнать сообщения, пришедшие, пока аккаунт был отключён."""
    with suppress(Exception):
        await asyncio.wait_for(client.catch_up(), 90)


async def get_client(slot):
    """Подключённый клиент аккаунта (создаёт подключение при необходимости) или None, если не авторизован."""
    client = pool.get(slot)
    if client is not None and client.is_connected():
        return client                              # быстрый путь: без замков и сети
    if slot in login_slots():
        return None                                # идёт вход: второй клиент на той же сессии «убил» бы её (AuthKeyDuplicated)
    async with slot_lock(slot):
        client = pool.get(slot)
        if client is not None and client.is_connected():
            return client
        await _drop(slot)
        if not session_exists(slot):
            return None
        client = create_client(slot)
        try:
            await asyncio.wait_for(client.connect(), CONNECT_TIMEOUT)
            if not await asyncio.wait_for(client.is_user_authorized(), 30):
                await client.disconnect()
                return None
            client.add_event_handler(make_dm_handler(slot), events.NewMessage(incoming=True))
        except BaseException:
            with suppress(Exception):
                await client.disconnect()
            raise
        pool[slot] = client
        dead_slots.discard(slot)
        with suppress(Exception):   # запоминаем, кто это за аккаунт (имя, @ник, id)
            me = await client.get_me()
            info = {"id": me.id, "name": " ".join(x for x in (me.first_name, me.last_name) if x),
                    "username": me.username or "", "phone": f"+{me.phone}" if getattr(me, "phone", None) else ""}
            if acc_info.get(slot) != info:
                acc_info[slot] = info
                save_json(ACC_INFO_FILE, acc_info)
        spawn(_catch_up(client))
        log.info("аккаунт %s подключён", slot)
        return client


async def drop_client(slot):
    async with slot_lock(slot):
        await _drop(slot)


async def connect_all():
    """Подключить все аккаунты с сессиями параллельно — чтобы они сразу слушали ЛС (бот при этом уже отвечает на команды)."""
    async def one(slot):
        try:
            await get_client(slot)
        except Exception as e:
            log.warning("аккаунт %s не подключился: %s: %s", slot, type(e).__name__, e)

    slots = [s for s in slots_sorted(load_config()) if session_exists(s)]
    await asyncio.gather(*(one(s) for s in slots))


async def drop_all():
    await asyncio.gather(*(drop_client(s) for s in list(pool)), return_exceptions=True)


async def purge_account(slot):
    """Убрать аккаунт насовсем: сессия, настройки, расписания, роли (вернуть можно только заново через /account и /login)."""
    slot = str(slot)
    await drop_client(slot)
    for suffix in (".session", ".session-journal"):
        with suppress(OSError):
            os.remove(session_file(slot) + suffix)
    cfg = load_config()
    cfg["accounts"].pop(slot, None)
    fix_roles(cfg)
    save_config(cfg)
    for store, path in ((acc_info, ACC_INFO_FILE), (spam_state, SPAM_FILE)):
        if store.pop(slot, None) is not None:
            save_json(path, store)
    dead_slots.discard(slot)
    dead_count.pop(slot, None)


async def check_slot(slot, tick):
    client = pool.get(slot)
    healthy = client is not None and client.is_connected()
    if healthy and tick % 6 == 0:                  # раз в ~3 минуты — настоящий пинг: ловим «полуживое» соединение
        try:
            await asyncio.wait_for(client(functions.PingRequest(ping_id=random.getrandbits(62))), 20)
        except Exception as e:
            log.warning("аккаунт %s не отвечает на пинг (%s) — переподключаю", slot, type(e).__name__)
            healthy = False
    if healthy:
        dead_count.pop(slot, None)
        return
    try:
        if client is not None:
            await drop_client(slot)
        new = await get_client(slot)
    except Exception as e:
        log.warning("аккаунт %s: переподключение не удалось: %s: %s", slot, type(e).__name__, e)
        return
    if new is None:
        # сессия не авторизована: вышли из аккаунта / завершили сеанс в Telegram. Подтверждаем несколько раз подряд
        # (чтобы случайный сбой не удалил аккаунт), потом убираем из списка насовсем.
        dead_count[slot] = dead_count.get(slot, 0) + 1
        dead_slots.add(slot)
        if dead_count[slot] >= DEAD_CONFIRMS and not run_locks:
            name = title(slot)
            await purge_account(slot)
            await notify_admins(f"{name} вышел из аккаунта — убран из списка насовсем.\n"
                                f"Вернуть: /account {slot}, затем /login {slot}")
    else:
        dead_count.pop(slot, None)
        log.info("аккаунт %s переподключён сторожем", slot)


async def watchdog_loop():
    """Следит, чтобы аккаунты всегда были подключены и слушали ЛС (раньше после обрыва связи никто не переподключал,
    пока вы сами не вызывали команду, и бот «молчал»)."""
    tick = 0
    await asyncio.sleep(20)
    while True:
        tick += 1
        cfg = load_config()
        busy = login_slots()
        slots = [s for s in slots_sorted(cfg) if session_exists(s) and s not in busy]
        await asyncio.gather(*(check_slot(s, tick) for s in slots), return_exceptions=True)
        await asyncio.sleep(30)


# ---------------------------------------------------------
# Спам-блок аккаунтов: проверка через @SpamBot
# ---------------------------------------------------------

MONTHS = {"янв": 1, "фев": 2, "мар": 3, "апр": 4, "мая": 5, "май": 5, "июн": 6, "июл": 7, "авг": 8, "сен": 9, "окт": 10,
          "ноя": 11, "дек": 12, "jan": 1, "feb": 2, "apr": 4, "may": 5, "jun": 6, "jul": 7, "aug": 8,
          "sep": 9, "oct": 10, "nov": 11, "dec": 12}
EN_MAR = "mar"  # англ. «mar» = март (в словаре рус. «мар»)
FREE_MARKERS = ("no limits", "free as a bird", "good news", "никаких ограничений", "добрые вести", "ограничений не",
                "не ограничен", "not limited", "no restrictions")
LIMIT_MARKERS = ("ограничен", "ограничения", "limited", "restricted", "annoying", "не понравились", "жалоб", "reports")
PERMANENT_MARKERS = ("навсегда", "permanent", "бессрочн", "until further notice", "неопределенный срок", "неопределённый срок")


def parse_spambot(text):
    """-> (status, until_ts|None, permanent). status: free | limited | unknown."""
    low = (text or "").lower().replace("ё", "е")
    if any(k in low for k in FREE_MARKERS):
        return "free", None, False
    until = None
    m = re.search(r"(\d{1,2})\s+([a-zа-я]+)\.?,?\s+(\d{4})(?:[^\d]{1,8}(\d{1,2}):(\d{2}))?", low)
    if m:
        key = m.group(2)[:3]
        month = MONTHS.get(key) or (3 if key == EN_MAR else None)
        if month:
            with suppress(ValueError):
                until = datetime(int(m.group(3)), month, int(m.group(1)), int(m.group(4) or 0), int(m.group(5) or 0), tzinfo=timezone.utc).timestamp()
    if until is None:
        m = re.search(r"(\d{4})-(\d{2})-(\d{2})(?:[ t](\d{2}):(\d{2}))?", low)
        if m:
            with suppress(ValueError):
                until = datetime(int(m.group(1)), int(m.group(2)), int(m.group(3)), int(m.group(4) or 0), int(m.group(5) or 0), tzinfo=timezone.utc).timestamp()
    permanent = any(k in low for k in PERMANENT_MARKERS)
    if until or permanent or any(k in low for k in LIMIT_MARKERS):
        return "limited", until, permanent
    return "unknown", None, False


def fmt_left(sec):
    sec = max(0, int(sec))
    d, rem = divmod(sec, 86400)
    h, rem = divmod(rem, 3600)
    m = rem // 60
    parts = ([f"{d} д"] if d else []) + ([f"{h} ч"] if h else []) + ([f"{m} мин"] if m and not d else [])
    return " ".join(parts) or "меньше минуты"


def is_blocked(slot):
    """Мут, из-за которого рассылку надо остановить: бессрочный или с датой окончания в будущем.
    «Ограничен, но срока нет» — это НЕ блок: рассылка идёт дальше."""
    s = spam_state.get(slot) or {}
    if s.get("status") != "limited":
        return False
    if s.get("permanent"):
        return True
    return bool(s.get("until")) and s["until"] > time.time()


def spam_line(slot):
    """Короткая строка о спам-блоке для панели. Пустая, если всё хорошо / нет данных."""
    s = spam_state.get(slot) or {}
    if s.get("status") == "limited":
        if s.get("permanent"):
            return "спам-блок: бессрочно"
        if s.get("until"):
            left = s["until"] - time.time()
            until = datetime.fromtimestamp(s["until"], SPAM_TZ).strftime("%d.%m %H:%M") + " МСК+4"
            return f"спам-блок: ещё <b>{fmt_left(left)}</b> (до {until})" if left > 0 else "срок блока истёк — проверьте /spam"
        return "Внимание: ограничен без срока — рассылка идёт"
    return ""


async def check_spambot(slot):
    """Зайти с аккаунта в @SpamBot, разобрать ответ и сохранить. Возвращает словарь состояния."""
    info = {"status": "unknown", "until": None, "permanent": False, "checked": time.time(), "text": ""}
    try:
        client = await get_client(slot)
        if client is None:
            info["text"] = "аккаунт не авторизован"
            return info
        async with client.conversation("SpamBot", timeout=25) as conv:
            await conv.send_message("/start")
            text = (await conv.get_response()).raw_text or ""
            with suppress(Exception):   # иногда SpamBot присылает второе сообщение с подробностями
                text += "\n" + ((await asyncio.wait_for(conv.get_response(), 5)).raw_text or "")
        status, until, permanent = parse_spambot(text)
        info.update(status=status, until=until, permanent=permanent, text=text.strip()[:400])
    except Exception as e:
        info["text"] = f"не удалось проверить: {type(e).__name__}"
        return info          # сбой проверки не затирает прежнее известное состояние
    spam_state[slot] = info
    save_json(SPAM_FILE, spam_state)
    return info


def spam_summary(slot, info):
    if info["status"] == "limited":
        if info.get("permanent"):
            return "ограничен бессрочно"
        if info.get("until"):
            left = info["until"] - time.time()
            until = datetime.fromtimestamp(info["until"], SPAM_TZ).strftime("%d.%m.%Y %H:%M") + " МСК+4"
            return f"спам-блок: осталось <b>{fmt_left(left)}</b> (до {until})" if left > 0 else "срок блока уже истёк"
        return "Внимание: ограничен без срока — рассылка идёт"
    if info["status"] == "free":
        return "ограничений нет"
    return f"не удалось разобрать ответ: «{esc(short(info.get('text') or '—', 200))}»"


# ---------------------------------------------------------
# Чаты и люди: статусы, админы, скан сообщений
# ---------------------------------------------------------

def status_text(st):
    if isinstance(st, UserStatusOnline):
        return "онлайн"
    if isinstance(st, UserStatusRecently):
        return "был(а) недавно"
    if isinstance(st, UserStatusLastWeek):
        return "был(а) на этой неделе"
    if isinstance(st, UserStatusLastMonth):
        return "был(а) в этом месяце"
    if isinstance(st, UserStatusOffline):
        return f"был(а) {st.was_online:%Y-%m-%d %H:%M} UTC"
    return "скрыт / давно"


def is_recently_active(user, max_days):
    st = getattr(user, "status", None)
    if isinstance(st, (UserStatusOnline, UserStatusRecently)):
        return True
    if isinstance(st, UserStatusLastWeek):
        return max_days >= 7
    if isinstance(st, UserStatusLastMonth):
        return max_days >= 30
    if isinstance(st, UserStatusOffline):
        was = st.was_online if st.was_online.tzinfo else st.was_online.replace(tzinfo=timezone.utc)
        return was >= datetime.now(timezone.utc) - timedelta(days=max_days)
    return False


def chat_names(entity, ref):
    """(полная подпись, короткая подпись): название / @юз / ID — что есть."""
    name = getattr(entity, "title", None) or " ".join(
        x for x in (getattr(entity, "first_name", None), getattr(entity, "last_name", None)) if x
    )
    uname = f"@{entity.username}" if getattr(entity, "username", None) else ""
    full = " · ".join(x for x in (name, uname, str(ref)) if x)
    return full, (name or uname or str(ref))


def full_chat_id(chat):
    return int(f"-100{chat.id}") if isinstance(chat, Channel) else -chat.id


def chat_key(entity):
    return ("c" if isinstance(entity, Channel) else "g", entity.id)


async def fetch_admins(client, entity, strict=False):
    """Все админы и владелец чата: [{id, username, name, bot, creator, rank}]."""
    out = []
    try:
        if isinstance(entity, Channel):
            users = await retry(lambda: client.get_participants(entity, filter=ChannelParticipantsAdmins))
        else:
            users = await retry(lambda: client.get_participants(entity))
        for u in users:
            p = getattr(u, "participant", None)
            kind = type(p).__name__
            creator = kind.endswith("Creator")
            if not (isinstance(entity, Channel) or creator or "Admin" in kind):
                continue
            out.append({
                "id": u.id,
                "username": (getattr(u, "username", None) or "").lower() or None,
                "name": " ".join(x for x in (getattr(u, "first_name", None), getattr(u, "last_name", None)) if x),
                "bot": bool(getattr(u, "bot", False)),
                "creator": creator,
                "rank": getattr(p, "rank", None),
            })
    except FloodWaitError:
        raise
    except Exception:
        if strict:
            raise
        return []
    return out


async def fetch_admin_ids(client, entity):
    return {a["id"] for a in await fetch_admins(client, entity)}


async def scan_messages(client, entity, limit, handle):
    """Идёт по последним сообщениям (от новых к старым), вызывает handle(msg, sender).
    При сбое Telegram ждёт и продолжает с того же места. Возвращает (просмотрено, неполно)."""
    seen = offset_id = attempts = 0
    while seen < limit:
        try:
            async for msg in client.iter_messages(entity, limit=limit - seen, offset_id=offset_id):
                check_stop()
                offset_id = msg.id
                seen += 1
                attempts = 0
                handle(msg, await msg.get_sender())
            return seen, False
        except TRANSIENT:
            attempts += 1
            if attempts > 5:
                return seen, True
            await interruptible_sleep(3 * attempts)
    return seen, False


async def first_access(clients, ref):
    """Первый аккаунт из списка, у которого есть доступ к чату: (client, entity)."""
    error = None
    for c in clients:
        try:
            return c, await retry(lambda c=c: resolve_chat(c, ref))
        except Exception as e:
            error = e
    if isinstance(error, ValueError) and "input entity" in str(error):
        raise RuntimeError("ни один аккаунт не состоит в этом чате (или неверный ID)")
    raise error


async def scan_chat(clients, ref, limit, max_days):
    """Источник: скан последних сообщений (боты и люди без юзернейма пропускаются, считается активность).
    Возвращает dict: short, chat_id, users {id: {username, active}}, admins {id}, partial."""
    client, entity = await first_access(clients, ref)
    _, short_name = chat_names(entity, ref)
    remember_chat(ref, short_name)
    users = {}
    cutoff = datetime.now(timezone.utc) - timedelta(days=max_days) if max_days > 0 else None

    def handle(msg, sender):
        if not isinstance(sender, User) or sender.id in users:
            return  # от новых к старым: первое попадание = последнее сообщение человека
        if sender.bot or sender.deleted or not sender.username:
            return
        date = msg.date if msg.date.tzinfo else msg.date.replace(tzinfo=timezone.utc)
        active = cutoff is None or date >= cutoff or is_recently_active(sender, max_days)
        users[sender.id] = {"username": sender.username.lower(), "active": active}

    _, partial = await scan_messages(client, entity, limit, handle)
    return {"short": short_name, "chat_id": tg_utils.get_peer_id(entity), "users": users,
            "admins": await fetch_admin_ids(client, entity), "partial": partial}


async def resolve_exclusion(clients, ref):
    """Чат-исключение: сообщения НЕ сканируются, проверка идёт по общим группам отправителя.
    clients = [сборщик, отправитель]. Если отправитель в чате не состоит — запасной вариант:
    список участников у того аккаунта, который в чате есть."""
    resolved, error = [], None
    for n, client in enumerate(clients):
        try:
            resolved.append((n, client, await retry(lambda client=client: resolve_chat(client, ref))))
        except Exception as e:
            error = e
    if not resolved:
        if isinstance(error, ValueError) and "input entity" in str(error):
            raise RuntimeError("ни один аккаунт не состоит в этом чате (или неверный ID)")
        raise error

    _, short_name = chat_names(resolved[0][2], ref)
    remember_chat(ref, short_name)
    admins = set()
    for _n, client, ent in resolved:
        admins |= await fetch_admin_ids(client, ent)

    members = set()
    if not any(n == 1 for n, _c, _e in resolved):   # отправитель в чате не состоит
        for _n, client, ent in resolved:
            with suppress(Exception):
                for u in await client.get_participants(ent, aggressive=True):
                    members.add(u.id)
    return {"short": short_name, "key": chat_key(resolved[0][2]), "admins": admins, "members": members}


async def common_chats(client, entity):
    """Все общие чаты аккаунта с человеком."""
    chats, max_id = [], 0
    while True:
        res = await retry(lambda: client(functions.messages.GetCommonChatsRequest(user_id=entity, max_id=max_id, limit=100)))
        batch = list(res.chats)
        chats += batch
        if len(batch) < 100:
            return chats
        max_id = batch[-1].id


async def excluded_by_common_groups(sender, entity, excl_keys):
    """Название чата-исключения, если он есть среди общих чатов отправителя с человеком, иначе None."""
    for ch in await common_chats(sender, entity):
        hit = excl_keys.get(chat_key(ch))
        if hit:
            return hit
    return None


def err_text(e):
    return str(e) if isinstance(e, RuntimeError) else f"{type(e).__name__}: {e}"


# ---------------------------------------------------------
# /run: скан чатов -> проверка по чатам-исключениям -> рассылка
# ---------------------------------------------------------

REASONS = {
    "UsernameNotOccupiedError": "юзернейм не найден",
    "UsernameInvalidError": "неверный юзернейм",
    "UserPrivacyRestrictedError": "закрыты личные сообщения",
    "UserIsBlockedError": "заблокировал аккаунт",
    "InputUserDeactivatedError": "аккаунт удалён",
    "PeerFloodError": "Flood",
}
FLOOD_STREAK = 10   # столько flood ПОДРЯД -> рассылка останавливается
MUTE_STOP = 2       # мут со сроком подтверждён в @SpamBot столько раз -> рассылка останавливается


def timed_mute(info):
    """Ответ SpamBot = мут со сроком (или бессрочный). «Ограничен без срока» и «ограничений нет» — не мут."""
    if not info or info.get("status") != "limited":
        return False
    return bool(info.get("permanent")) or bool(info.get("until") and info["until"] > time.time())


async def confirm_mute(slot, checks=MUTE_STOP):
    """Пишет @SpamBot /start до `checks` раз. Мут подтверждён, только если КАЖДАЯ проверка показала мут со сроком —
    любая проверка без мута (или «ограничен, но срока нет») значит: рассылка продолжается."""
    info = {}
    for i in range(checks):
        if i:
            await interruptible_sleep(4)
        info = await check_spambot(slot)
        if not timed_mute(info):
            return False, info
    return True, info


def reason_of(e):
    if isinstance(e, FloodWaitError):
        return f"FloodWait {e.seconds} с"
    if isinstance(e, RuntimeError):
        return str(e)
    return REASONS.get(type(e).__name__) or type(e).__name__


def person_line(icon, name, uid, info, tail=""):
    """Ошибка: @username (id) · Группа (id группы) · причина"""
    line = f"{icon} @{esc(name)} (<code>{uid}</code>) · {esc(short(info['chat'], 30))} (<code>{info['chat_id']}</code>)"
    return line + (f" · {esc(tail)}" if tail else "")


async def with_flood_wait(fn, cap=300):
    """Повторяет запрос, пережидая короткий FloodWait (длиннее cap — пробрасывает ошибку)."""
    try:
        return await fn()
    except FloodWaitError as e:
        if e.seconds > cap:
            raise
        await interruptible_sleep(e.seconds + 1)
        return await fn()


def pick_collector(cfg, snd):
    """Сборщик для запуска от имени отправителя snd: из /collector, а если это тот же аккаунт — любой другой со входом."""
    col = cfg["roles"]["collector"]
    if col and col != snd and col in cfg["accounts"] and session_exists(col):
        return col
    for s in slots_sorted(cfg):
        if s != snd and session_exists(s):
            return s
    return col


def run_cfg(cfg, snd=None, col=None, chats=None):
    """Конфиг запуска: роли + источники и БС именно этого аккаунта-отправителя (его личные режимы чатов).
    chats — если задан, берём только эти чаты из его источников (чаты конкретного расписания)."""
    cfg = copy.deepcopy(cfg)
    if snd:
        cfg["roles"]["sender"] = snd
    if col:
        cfg["roles"]["collector"] = col
    src, exc = account_chats(cfg, cfg["roles"]["sender"])
    if chats is not None:
        keep = {str(c) for c in chats}
        src = [r for r in src if r in keep]
    cfg["chat_source_groups"], cfg["chat_exclude_groups"] = src, exc
    return cfg


async def run_collection_and_send(message, cfg, uid):
    if run_locks:
        await notify(message, "Внимание: Рассылка уже идёт. Остановить: /stop")
        return
    run_locks.add(uid)
    stats = {"sent": 0, "failed": 0, "excluded": 0}

    def extra():
        return f"{stats['sent']} · {stats['failed']} · {stats['excluded']}"

    try:
        await run_op(message, "Рассылка", lambda: run_job(message, cfg, stats), extra)
    finally:
        run_locks.discard(uid)


async def run_job(message, cfg, stats):
    t0 = time.monotonic()
    sources, excludes = cfg["chat_source_groups"], cfg["chat_exclude_groups"]
    col, snd = cfg["roles"]["collector"], cfg["roles"]["sender"]
    if not col or not snd or col not in cfg["accounts"] or snd not in cfg["accounts"]:
        await notify(message, "Ошибка: Нужно минимум два аккаунта: сборщик и отправитель. Добавьте: /account N")
        return
    if not sources:
        await notify(message, f"Ошибка: Нет чатов в режиме ИСТ для {title(snd)}. Настройте: /chats")
        return
    if col == snd:
        await notify(message, "Ошибка: Сборщик и отправитель — один аккаунт. Назначьте разные: /collector, /sender")
        return
    msgs = [str(m) for m in (cfg.get("messages") or []) if str(m).strip()][:1]   # первое сообщение — один текст
    if not msgs:
        await notify(message, "Ошибка: Нет текстов первого сообщения. Добавьте: /text")
        return
    limit, max_days = int(cfg["scan_messages_limit"]), int(cfg["max_inactive_days"])
    max_messages, delay = int(cfg["max_messages"]), float(cfg["delay_between_messages"])

    if not await is_authorized(col):
        await notify(message, f"Ошибка: {title(col)} (сборщик) не авторизован: /login {col}")
        return
    sender = await get_client(snd)
    if sender is None:
        await notify(message, f"Ошибка: {title(snd)} (отправитель) не авторизован: /login {snd}")
        return
    if is_blocked(snd):   # раньше был мут — дважды перепроверяем в @SpamBot (/start), мут мог уже кончиться
        muted, sb = await confirm_mute(snd)
        if muted:
            await notify(message, f"Остановлено: {title(snd)} под спам-блоком (подтверждено {MUTE_STOP} раза)\n{spam_summary(snd, sb)}\n\n"
                                  "Поставьте другого отправителя: /sender N или /swap")
            return

    await notify(message, f"<b>ЗАПУСК РАССЫЛКИ</b>\n{LINE}\nСборщик: {title(col)}\nОтправитель: {title(snd)}")
    link_txt = link_text_of(cfg)
    if not link_txt:
        await notify(message, "Внимание: Текст со ссылкой не задан (/text2): тем, кто согласится, отправить будет нечего.")
    else:
        lk, _nm = await check_invite(sender, link_txt)
        if lk == "expired":
            await notify(message, "Внимание: <b>Ссылка в /text2 истекла или отозвана.</b> Рассылка идёт, но согласившимся ссылка "
                                  "не уйдёт, пока вы её не обновите (/text2).")

    # 1-2. Скан чатов-источников и подготовка чатов-исключений
    found, admins, own_ids = {}, set(), set()
    excl_keys, excl_members = {}, {}
    src_lines, exc_lines = [], []
    async with account_client(col) as collector, working(message, "Сканирую чаты…"):
        clients = [collector, sender]
        for c in clients:
            with suppress(Exception):
                own_ids.add((await c.get_me()).id)
        for ref in sources:
            check_stop()
            try:
                res = await scan_chat(clients, ref, limit, max_days)
            except Exception as e:
                src_lines.append(f"Внимание: <code>{esc(ref)}</code> · {esc(err_text(e))}")
                continue
            active = {i: u for i, u in res["users"].items() if u["active"]}
            for i, u in active.items():
                found.setdefault(i, {"username": u["username"], "chat": res["short"], "chat_id": res["chat_id"]})
            admins |= res["admins"]
            log_event("found", col, None, chat=res["short"], ref=res["chat_id"], n=len(active))
            src_lines.append(f"• {esc(res['short'])} · <b>{len(active)}</b>" + (" скан неполный" if res["partial"] else ""))
        for ref in excludes:
            check_stop()
            try:
                res = await resolve_exclusion(clients, ref)
            except Exception as e:
                exc_lines.append(f"Внимание: <code>{esc(ref)}</code> · {esc(err_text(e))}")
                continue
            excl_keys[res["key"]] = res["short"]
            for i in res["members"]:
                excl_members.setdefault(i, res["short"])
            admins |= res["admins"]
            exc_lines.append(f"• {esc(res['short'])}")

    if excludes and not excl_keys:
        await notify(message, "Ошибка: Ни один чат-исключение не удалось проверить — запуск остановлен, "
                              "чтобы не написать исключённым.\n" + "\n".join(exc_lines))
        return

    blocked = admins | own_ids
    processed, messaged = read_processed(), messaged_ids()
    free = {i: u for i, u in found.items() if i not in blocked}
    done_before = {i for i, u in free.items() if u["username"] in processed or i in messaged}
    queue = sorted(((i, u) for i, u in free.items() if i not in done_before), key=lambda x: x[1]["username"])
    n_adm = sum(1 for i in found if i in admins)
    await notify(
        message,
        "<b>ИСТОЧНИКИ</b>\n" + "\n".join(src_lines)
        + ("\n\n<b>БЕЛЫЙ СПИСОК</b>\n" + "\n".join(exc_lines) if exc_lines else "")
        + f"\n{LINE}\nНайдено: <b>{len(found)}</b> · админов: {n_adm} · уже писали: {len(done_before)}\n"
        f"К проверке: <b>{len(queue)}</b>")
    if not queue:
        return

    # 3-4. Проверка по чатам-исключениям идёт В ФОНЕ параллельно с рассылкой: несколько проверяющих сразу берут людей
    # из очереди и отдают чистых отправителю. Рассылка не ждёт конца проверки, но НИКОМУ не пишет до его проверки.
    stopped = None
    ready_q = asyncio.Queue()
    chk = {"clean": 0, "stop": False, "flood": 0}
    status = None
    pending = iter(queue)

    async def check_worker():
        try:
            for uid_, info in pending:             # один общий итератор: каждый человек достаётся одному проверяющему
                if chk["clean"] >= max_messages or chk["stop"]:
                    return
                check_stop()
                name = info["username"]
                if uid_ in excl_members:
                    stats["excluded"] += 1
                    log_event("excl", snd, uid_, name=name, chat=info["chat"], ref=info["chat_id"])
                    continue
                step, hit = "поиск", None
                try:
                    entity = await with_flood_wait(lambda: retry(lambda: sender.get_entity(name)))
                    if getattr(entity, "bot", False) or getattr(entity, "deleted", False):
                        raise RuntimeError("бот или удалённый аккаунт")
                    if excl_keys:
                        step = "исключения"
                        hit = await with_flood_wait(lambda: retry(lambda: excluded_by_common_groups(sender, entity, excl_keys)))
                except FloodWaitError as e:
                    chk["flood"], chk["stop"] = e.seconds, True
                    return
                except Exception as e:             # не смогли проверить — на всякий случай не пишем
                    stats["failed"] += 1
                    log_event("fail", snd, uid_, name=name, chat=info["chat"], ref=info["chat_id"], w=short(reason_of(e), 40))
                    continue
                if hit:
                    stats["excluded"] += 1
                    log_event("excl", snd, uid_, name=name, chat=info["chat"], ref=info["chat_id"])
                    continue
                chk["clean"] += 1
                ready_q.put_nowait((uid_, name, entity, info))
        except StopRun:
            chk["stop"] = True

    async def checker():
        try:
            await asyncio.gather(*(check_worker() for _ in range(3)))
        finally:
            ready_q.put_nowait(None)               # сигнал «проверять больше некого»
            if status is not None:
                with suppress(Exception):
                    await status.delete()

    check_task = asyncio.create_task(checker())
    try:
        floods, mutes, attempts, started = 0, 0, 0, False
        while True:
            item = await ready_q.get()
            if item is None:
                break
            if attempts >= max_messages:           # проверяющие могли набрать чуть больше лимита — лишних не пишем
                break
            uid_, name, entity, info = item
            if not started:
                started = True
                await notify(message, f"<b>Рассылка идёт в фоне</b> · до {min(len(queue), max_messages)} чел.\n"
                                      "<i>Сюда будут приходить только ответы людей и отправленные ссылки.</i>")
            check_stop()
            if attempts:
                await interruptible_sleep(delay)
            attempts += 1
            reserved = False   # человек записан ДО отправки, чтобы при сбое/остановке не получить сообщение дважды

            def unreserve():
                remove_processed(name)
                unset_dm_state(snd, entity.id)

            try:
                append_processed(name)
                set_dm_state(snd, entity.id, "text1")
                set_dm_meta(snd, entity.id, {"chat": info["chat"], "ref": info["chat_id"], "name": name,
                                             "ts": time.time(), "replied": False})
                reserved = True
                await asyncio.shield(sender.send_message(
                    entity, fmt_text(random.choice(msgs), {"chat": info["chat"], "name": name}, entity)))   # даже жёсткий стоп не оборвёт отправку
                reserved, floods, mutes = False, 0, 0
                stats["sent"] += 1
                log_event("sent", snd, entity.id, name=name, chat=info["chat"], ref=info["chat_id"])
            except (PeerFloodError, FloodWaitError) as e:
                if reserved:
                    unreserve()
                floods += 1
                stats["failed"] += 1
                log_event("fail", snd, entity.id, name=name, chat=info["chat"], ref=info["chat_id"], w=short(reason_of(e), 40))
                if isinstance(e, FloodWaitError) and e.seconds > 300:
                    stopped = f"FloodWait {e.seconds} с — рассылка остановлена."
                elif floods >= FLOOD_STREAK:
                    sb = await check_spambot(snd)
                    stopped = (f"<b>{FLOOD_STREAK} flood подряд — рассылка остановлена.</b>\n"
                               f"{title(snd)}: {spam_summary(snd, sb)}\n"
                               "Поставьте другого отправителя: /sender N или /swap")
                elif isinstance(e, PeerFloodError):
                    # flood сам по себе не повод останавливаться: пишем @SpamBot /start и смотрим, есть ли мут со сроком
                    sb = await check_spambot(snd)
                    if timed_mute(sb):
                        mutes += 1
                        if mutes >= MUTE_STOP:
                            stopped = (f"<b>Мут подтверждён {MUTE_STOP} раза — рассылка остановлена.</b>\n"
                                       f"{title(snd)}: {spam_summary(snd, sb)}\n"
                                       "Поставьте другого отправителя: /sender N или /swap")
                elif isinstance(e, FloodWaitError):
                    await interruptible_sleep(e.seconds + 1)
            except TRANSIENT as e:
                # сбой связи: сообщение могло дойти — оставляем в «уже писали», чтобы не отправить повторно
                floods = 0
                stats["failed"] += 1
                log_event("fail", snd, entity.id, name=name, chat=info["chat"], ref=info["chat_id"], w=f"{type(e).__name__} (мог дойти)")
            except Exception as e:
                if reserved:
                    unreserve()
                floods = 0
                stats["failed"] += 1
                log_event("fail", snd, entity.id, name=name, chat=info["chat"], ref=info["chat_id"], w=short(reason_of(e), 40))
            if stopped:
                break
        if stopped is None and chk["flood"]:
            stopped = f"FloodWait {chk['flood']} с при проверке — рассылка остановлена."
    finally:
        chk["stop"] = True                         # остановить проверяющих, если рассылка закончилась раньше
        if not check_task.done():
            check_task.cancel()
            with suppress(Exception, asyncio.CancelledError):
                await check_task
        if status is not None:
            with suppress(Exception):
                await status.delete()

    sec = int(time.monotonic() - t0)
    await notify(
        message,
        ("<b>РАССЫЛКА ПРЕРВАНА</b>" if stopped else "<b>РАССЫЛКА ЗАВЕРШЕНА</b>") + f" · {sec // 60}:{sec % 60:02d}\n"
        f"{LINE}\nОтправлено: <b>{stats['sent']}</b> · ошибок: {stats['failed']} · исключено: {stats['excluded']}\n"
        "Подробно: /stats"
        + (f"\n\n{stopped}" if stopped else ""))


# ---------------------------------------------------------
# /start и /command
# ---------------------------------------------------------

LINE = "━━━━━━━━━━━━━━━━━━"

COMMANDS_TEXT = f"""<b>СПРАВКА ПО КОМАНДАМ</b>
{LINE}

<b>Рассылка</b>
/run — запуск: скан → проверка → отправка
/stop — остановить
/reset — забыть, кому уже писали

<b>Аккаунты</b>
/account N — добавить аккаунт
/login N — войти (по номеру или QR)
/logout N — выйти и удалить
/collector N · /sender N — кто собирает / кто пишет
/swap — поменять роли местами
/spam — проверка спам-блока
/stats — статистика: сводка, аккаунты, группы, время, дни
<i>Пришлите ID или @юзер — получите сводку по всем аккаунтам: приглашали ли, с какого, когда, из какого чата, просил ли ссылку, приоритет ЗП / КП.
Перешлите уведомление #НОВЫЙ_ПОЛЬЗОВАТЕЛЬ — бот запишет вход в группу, сверит человека со своими записями и определит приоритет</i>

<b>Вкладки</b>
В /chats и /schedule сверху ряд вкладок: переключайтесь, добавляйте «＋ Вкладка», переименовывайте и удаляйте.
В /chats номер чата переносит его в следующую вкладку, в расписании — кнопка «Вкладка»

<b>Чаты</b>
/chats — общий список: <b>ИСТ</b> (откуда берём) · <b>БС</b> (белый список, им не пишем) · <b>ОТКЛ</b>
Кнопка <b>Пр</b> у чата — приоритет ЗП или КП: человек из чата ЗП (или состоящий в нём) считается ЗП
/source @чат · /exclude @чат — быстро добавить как ИСТ / БС
<i>Чаты добавляются по одному</i>

<b>Автоматизация</b>
/schedule — расписание запусков
/auto — автоответы вкл/выкл

<b>Тексты</b>
/text — первое сообщение
/text2 — <b>ссылка</b>: уходит, когда человек согласился (бот проверяет, что она не истекла)
/text3 — ответы на отказ (по порядку)
/text4 — ответы на вопрос и сомнение (по порядку)
/text5 — ответы на «откуда мой контакт?» (по порядку)
/text6 — <b>лимит на день</b>: уходит вместо ссылки, когда места на сегодня кончились
<i>В текстах: {{chat}} — чат, где нашли человека · {{name}} — имя</i>

<b>Параметры</b>
/limit — сколько писать за запуск
/scan — сколько сообщений сканировать
/active — давность активности, дней
/delay — пауза между отправками, сек
/wait — через сколько часов без ответа удалять диалог у обоих
/daylimit — скольким людям в день выдавать ссылку на группу (0 — без лимита)
/dayreset — обнулить сегодняшний счётчик ссылок

<b>Инструменты</b>
/info — всё о человеке (@юзер или ID)
/admin_list — админы чата
/scan_group — файл с людьми чата
/cancel — отменить ввод"""


def btn(text, data):
    return InlineKeyboardButton(text=text, callback_data=data)


def start_kb():
    return InlineKeyboardMarkup(inline_keyboard=[
        [btn("Запуск", "m:run"), btn("Стоп", "m:stop")],
        [btn("Аккаунты", "m:acc"), btn("Чаты", "cm:g:v")],
        [btn("Расписание", "sc:home"), btn("Тексты", "st:texts")],
        [btn("Статистика", "m:stats"), btn("Настройки", "st:home")],
        [btn("Команды", "cmds")]])


def back_kb():
    return InlineKeyboardMarkup(inline_keyboard=[[InlineKeyboardButton(text="Назад", callback_data="home")]])


def slot_state(slot):
    """ok — подключён; login — идёт вход; offline — сессия есть, но соединения нет; none — не вошли."""
    if slot in login_slots():
        return "login"
    c = pool.get(slot)
    if c is not None and c.is_connected():
        return "ok"
    return "offline" if session_exists(slot) else "none"


async def accounts_text(cfg):
    """Короткий список: статус · номер · имя/@ник · роль. Статус берётся из пула без сетевых запросов —
    /start отвечает мгновенно, даже если какой-то аккаунт сейчас переподключается."""
    shown = slots_sorted(cfg)          # все аккаунты всегда на своих местах, вышедшие — с 
    icons = {"ok": "[в сети]", "login": "[вход]", "offline": "[нет связи]", "none": "[не настроен]"}
    rows = []
    for slot in shown:
        st = slot_state(slot)
        info = acc_info.get(slot) or {}
        who = " ".join(x for x in (esc(info.get("name") or ""), f"@{esc(info['username'])}" if info.get("username") else "") if x)
        who = who or esc(cfg["accounts"][slot]["phone"] or "не настроен")
        row = f"{icons[st]} <b>{slot}</b> · {who}{role_mark(cfg, slot)}"
        if st == "none":
            row += f" · /login {slot}"
        elif st == "offline":
            row += " · переподключается…"
        elif st == "login":
            row += " · идёт вход"
        extra = [x for x in (spam_line(slot),) if x]
        rows.append(row + "".join("\n      " + x for x in extra))
    return "\n".join(rows) if rows else "нет аккаунтов — /account 1"


async def dashboard():
    cfg = load_config()
    n_src, n_bs = len(cfg["chat_source_groups"]), len(cfg["chat_exclude_groups"])
    n_off = len(cfg["chat_modes"]) - n_src - n_bs
    ents = [e for a in cfg["accounts"].values() for e in (a.get("schedule") or [])]
    status = f"идёт: <b>{esc(', '.join(o.name for o in ops))}</b> · /stop" if ops else "ожидание"
    return (
        "<b>ПАНЕЛЬ УПРАВЛЕНИЯ</b>\n"
        f"{LINE}\n"
        f"<b>Статус:</b> {status}\n\n"
        "<b>Аккаунты</b>\n" + await accounts_text(cfg) + "\n"
        f"{LINE}\n"
        f"<b>Чаты:</b> ИСТ {n_src} · БС {n_bs} · ОТКЛ {n_off}\n"
        f"<b>Расписаний:</b> {len(ents)} (вкл {sum(1 for e in ents if e.get('on', True))})\n"
        f"<b>Автоответы:</b> {'вкл' if cfg['dm_reply_enabled'] else 'выкл'}\n"
        f"<b>Текст со ссылкой:</b> {'задан' if link_text_of(cfg) else 'Внимание: не задан (/text2)'}\n"
        f"<b>Ссылок сегодня:</b> {day_line(cfg)} (/daylimit)\n"
        f"<b>Написано всего:</b> {len(read_processed())}\n"
        f"{LINE}\n"
        "/run · /stop")


async def do_swap():
    cfg = load_config()
    r = cfg["roles"]
    r["collector"], r["sender"] = r["sender"], r["collector"]
    save_config(cfg)
    return r


def do_reset():
    for path in (PROCESSED_FILE, DM_STATES_FILE, DM_META_FILE, REPLY_MAP_FILE):
        _save_pending.pop(path, None)
        with suppress(FileNotFoundError):
            os.remove(path)
    dm_states.clear()
    dm_meta.clear()
    reply_map.clear()
    dm_by_uid.clear()


@router.message(Command("start", "accounts"))
@admin
async def cmd_start(message: Message):
    await notify(message, await dashboard(), start_kb())


@router.message(Command("command", "help"))
@admin
async def cmd_command(message: Message):
    await notify(message, COMMANDS_TEXT)


async def spam_check_all(message, slots=None):
    cfg = load_config()
    slots = slots or [s for s in slots_sorted(cfg) if session_exists(s)]
    if not slots:
        await notify(message, "Ошибка: Нет авторизованных аккаунтов.")
        return
    lines = []
    async with working(message, "Проверяю SpamBot…"):
        for slot in slots:
            check_stop()
            info = await check_spambot(slot)
            lines.append(f"<b>{title(slot)}</b>\n{spam_summary(slot, info)}")
    await notify(message, "<b>SpamBot</b>\n\n" + "\n\n".join(lines))


@router.message(Command("spam"))
@admin
@operation("Проверка SpamBot")
async def cmd_spam(message: Message):
    args = args_of(message)
    await spam_check_all(message, [args[0]] if args and args[0] in load_config()["accounts"] else None)


# ---------------------------------------------------------
# Кнопки: только «Команды» в /start и управление списками чатов
# ---------------------------------------------------------

@router.callback_query()
@admin
async def on_button(call: CallbackQuery):
    data = call.data or ""
    if data.startswith("sv:"):
        _, sec, per = (data.split(":") + ["sum", "t"])[:3]
        await call.answer()
        with suppress(Exception):
            await edit(call.message, stats_text(sec, per), stats_kb(sec, per))
        return
    if data.startswith("m:"):
        act = data[2:]
        if act == "run":
            await call.answer("Запускаю…")
            await run_collection_and_send(call.message, run_cfg(load_config()), call.from_user.id)
        elif act == "stop":
            n = request_stop()
            await call.answer("Останавливаю…" if n else "Сейчас ничего не запущено", show_alert=not n)
        elif act == "stats":
            await call.answer()
            await notify(call.message, stats_text("sum", "t"), stats_kb("sum", "t"))
        else:                                # m:acc — обновить панель
            await call.answer("Обновлено")
            await edit(call.message, await dashboard(), start_kb())
        return
    if data == "cmds":
        await call.answer()
        await edit(call.message, COMMANDS_TEXT, back_kb())     # правим то же сообщение, а не шлём новое
        return
    if data == "home":
        await call.answer()
        await edit(call.message, await dashboard(), start_kb())
        return
    if data.startswith("st:"):
        await settings_button(call, data.split(":")[1:])
        return
    if data.startswith("sc:"):
        await sched_button(call, data.split(":")[1:])
        return
    if data.startswith("tb:"):
        await tab_button(call, data.split(":")[1:])
        return
    if data.startswith("lg:"):
        await login_button(call, data.split(":")[1:])
        return
    if data.startswith("cm:"):
        parts = data.split(":")              # cm:<g|слот>:<действие>[:аргументы]
        if len(parts) >= 3:
            await chat_modes_button(call, parts[1], parts[2], parts[3:])
            return
    if data.startswith("tx:"):
        parts = data.split(":", 3)           # tx:<список>:<действие>[:<номер>]
        if len(parts) >= 3 and parts[1] in TEXT_LISTS:
            await text_button(call, parts[1], parts[2], parts[3] if len(parts) > 3 else None)
            return
    await call.answer()


@router.message(Command("cancel"))
@admin
async def cmd_cancel(message: Message):
    await close_login(message.from_user.id)
    waiting.pop(message.from_user.id, None)
    await notify(message, "Отменено")


@router.message(Command("reset"))
@admin
async def cmd_reset(message: Message):
    do_reset()
    await notify(message, "Прогресс сброшен")


@router.message(Command("run"))
@admin
async def cmd_run(message: Message):
    await run_collection_and_send(message, run_cfg(load_config()), message.from_user.id)


@router.message(Command("stop"))
@admin
async def cmd_stop(message: Message):
    n = request_stop()
    await notify(message, "Останавливаю… дождусь завершения текущего шага (до ~12 сек)." if n else "Сейчас ничего не запущено.")


@router.message(Command("swap"))
@admin
async def cmd_swap(message: Message):
    r = await do_swap()
    await notify(message, f"Сборщик: <b>{title(r['collector'])}</b>, отправитель: <b>{title(r['sender'])}</b>")


@router.message(Command("collector", "sender"))
@admin
async def cmd_role(message: Message):
    role = "collector" if message.text.split()[0].lstrip("/").startswith("collector") else "sender"
    other = "sender" if role == "collector" else "collector"
    cfg = load_config()
    args = args_of(message)
    if not args or args[0] not in cfg["accounts"]:
        await notify(message, f"Использование: /{role} N\nАккаунты: {', '.join(slots_sorted(cfg))}")
        return
    if cfg["roles"][other] == args[0]:
        await notify(message, "Ошибка: Этот аккаунт уже занят другой ролью. Используйте /swap.")
        return
    cfg["roles"][role] = args[0]
    save_config(cfg)
    await notify(message, f"{'Сборщик' if role == 'collector' else 'Отправитель'}: <b>{title(args[0])}</b>")


# ---------------------------------------------------------
# Чаты-источники и чаты-исключения: добавление по одному, удаление, очистка
# ---------------------------------------------------------

async def lookup_chat_name(ref):
    """Название чата (проверка, что хоть один аккаунт его видит) или None."""
    async def job(client, entity, slot):
        return chat_names(entity, ref)[1]
    try:
        _, name = await asyncio.wait_for(with_chat_access(ref, job), 90)
    except Exception:
        return None
    remember_chat(ref, name)
    return name


# ---------------------------------------------------------
# Чаты: один общий список, у каждого режим ИСТ / БС / ОТКЛ (+ личные поправки у аккаунтов)
# ---------------------------------------------------------

def chash(ref):
    return hashlib.md5(str(ref).encode()).hexdigest()[:8]


def ref_by_hash(refs, h):
    return next((r for r in refs if chash(r) == h), None)


def pages_of(text, limit=3500):
    """Текст -> список кусков, каждый влезает в сообщение Telegram."""
    out = []
    for chunk in split_text(text, limit):
        while len(chunk) > 4000:
            out.append(chunk[:3900])
            chunk = chunk[3900:]
        out.append(chunk)
    return out or [""]


async def send_pages(message, text, kb=None):
    pages = pages_of(text)
    for i, page in enumerate(pages):
        await notify(message, page, kb if i == len(pages) - 1 else None)


async def show_pages(call, text, kb=None):
    """Обновить сообщение с кнопками; если текст длиннее одного сообщения — прислать заново несколькими."""
    pages = pages_of(text)
    if len(pages) == 1:
        await edit(call.message, pages[0], kb)
        return
    with suppress(Exception):
        await call.message.delete()
    await send_pages(call.message, text, kb)


def cur_tab(cfg):
    """Открытая сейчас вкладка: id или "*" (все)."""
    t = ui_tab.get("id")
    ids = tab_ids(cfg)
    if t == "*" and len(ids) > 1:
        return "*"
    return t if t in ids else ids[0]


def tab_chats(cfg):
    cur = cur_tab(cfg)
    return [r for r in cfg["chat_modes"] if cur == "*" or tab_of_chat(cfg, r) == cur]


def tab_bar(cfg, sec, tag, counts):
    """Ряд вкладок сверху: переключение, «＋», переименование, удаление. sec: c — чаты, s — расписание аккаунта, h — главная расписания."""
    cur = cur_tab(cfg)
    base = f"tb:{sec}:{tag}"
    tabs = cfg["tabs"]
    btns = []
    if len(tabs) > 1:
        btns.append(btn(("● " if cur == "*" else "") + f"Все ({sum(counts.values())})", f"{base}:v:*"))
    for t in tabs:
        btns.append(btn(("● " if cur == t["id"] else "") + f"{short(t['name'], 14)} ({counts.get(t['id'], 0)})", f"{base}:v:{t['id']}"))
    rows = [btns[i:i + 3] for i in range(0, len(btns), 3)]
    ctrl = []
    if len(tabs) < MAX_TABS:
        ctrl.append(btn("＋ Вкладка", f"{base}:a"))
    if cur != "*":
        ctrl.append(btn("Переименовать", f"{base}:n"))
        if len(tabs) > 1:
            ctrl.append(btn("Удалить вкладку", f"{base}:x"))
    if ctrl:
        rows.append(ctrl)
    return rows


def render_section(sec, tag):
    if sec == "c":
        return chat_modes_view(None if tag == "g" else tag)
    if sec == "s":
        return sched_account_view(tag)
    return sched_home_view()


def new_tab_id(cfg):
    while True:
        tid = f"{random.getrandbits(16):04x}"
        if tid not in tab_ids(cfg):
            return tid


async def tab_button(call, parts):
    """tb:<раздел>:<тег>:<действие>[:<id>]"""
    if len(parts) < 3:
        await call.answer()
        return
    sec, tag, act = parts[:3]
    arg = parts[3] if len(parts) > 3 else None
    uid = call.from_user.id
    cfg = load_config()
    toast = None
    if act == "v":
        if arg == "*" or arg in tab_ids(cfg):
            ui_tab["id"] = arg
    elif act == "a":
        if len(cfg["tabs"]) >= MAX_TABS:
            await call.answer(f"Максимум вкладок: {MAX_TABS}", show_alert=True)
            return
        waiting[uid] = f"tabadd:{sec}:{tag}"
        await call.answer()
        await notify(call.message, "Отправьте название новой вкладки (до 24 символов).\nОтмена: /cancel")
        return
    elif act == "n":
        cur = cur_tab(cfg)
        if cur == "*":
            await call.answer("Откройте конкретную вкладку", show_alert=True)
            return
        waiting[uid] = f"tabren:{sec}:{tag}:{cur}"
        await call.answer()
        await notify(call.message, f"Новое название для вкладки «{esc(tab_name(cfg, cur))}» (до 24 символов).\nОтмена: /cancel")
        return
    elif act == "x":
        cur = cur_tab(cfg)
        if cur == "*" or len(cfg["tabs"]) <= 1:
            await call.answer("Последнюю вкладку удалить нельзя", show_alert=True)
            return
        cfg["tabs"] = [t for t in cfg["tabs"] if t["id"] != cur]
        fix_tabs(cfg)                              # снимает привязки чатов к удалённой вкладке
        first = cfg["tabs"][0]["id"]
        for acc in cfg["accounts"].values():
            for e in acc.get("schedule") or []:
                if e.get("tab") == cur:
                    e["tab"] = first
        save_config(cfg)
        ui_tab["id"] = first
        toast = f"Удалено. Чаты и расписания перенесены в «{tab_name(cfg, first)}»"
    view = render_section(sec, tag)
    if view is None:
        await call.answer("Это уже удалено", show_alert=True)
        return
    await call.answer(toast)
    await show_pages(call, *view)


def chat_modes_view(slot=None):
    cfg = load_config()
    all_refs = list(cfg["chat_modes"])
    cur = cur_tab(cfg)
    refs = tab_chats(cfg)
    multi = len(cfg["tabs"]) > 1
    modes = effective_modes(cfg, slot)
    own = ((cfg["accounts"].get(slot) or {}).get("chat_modes") or {}) if slot else {}
    prios = cfg.get("chat_priority") or {}
    tag = slot or "g"
    counts = {m: sum(1 for r in refs if modes[r] == m) for m in CHAT_MODES}
    tcounts = Counter(tab_of_chat(cfg, r) for r in all_refs)
    scope = "все" if cur == "*" else tab_name(cfg, cur)
    if slot:
        head = (f"<b>ЧАТЫ · {title(slot)}</b> ({len(refs)})\n<i>Личные настройки этого аккаунта: * — свой режим, "
                "без значка — как в общем списке (↺ вернуть общий).</i>")
    else:
        head = f"<b>ЧАТЫ</b> ({len(refs)})"
    head += f"\nВкладка: <b>{esc(scope)}</b>"
    legend = ("<b>ИСТ</b> — откуда берём людей\n<b>БС</b> — белый список: этим людям не пишем\n"
              "<b>ОТКЛ</b> — выключен, просто висит в списке\n"
              "<b>Пр</b> — приоритет чата: ЗП или КП. Человек, который состоит хотя бы в одном чате ЗП, "
              "считается ЗП, даже если взят из другого чата")
    if multi:
        legend += "\n<b>Номер</b> — перенести чат в следующую вкладку"
    rows = []
    for n, ref in enumerate(refs, 1):
        name = chat_name_cache.get(ref)
        label = f"<b>{esc(name)}</b> · <code>{esc(ref)}</code>" if name else f"<code>{esc(ref)}</code>"
        pr = prios.get(ref)
        rows.append(f"{n}. {label} — <b>{MODE_LABEL[modes[ref]]}</b>" + (f" · <b>{PRIO_NAME[pr]}</b>" if pr in ("zp", "kp") else "")
                    + (" *" if ref in own else "")
                    + (f" · [{esc(tab_name(cfg, tab_of_chat(cfg, ref)))}]" if multi and cur == "*" else ""))
    n_zp = sum(1 for r in refs if prios.get(r) == "zp")
    n_kp = sum(1 for r in refs if prios.get(r) == "kp")
    text = (f"{head}\n{legend}\n\nИтого: ИСТ {counts['src']} · БС {counts['bs']} · ОТКЛ {counts['off']} · ЗП {n_zp} · КП {n_kp}\n\n"
            + ("\n".join(rows) if rows else "<i>в этой вкладке пусто — нажмите «Добавить»</i>"))
    kb = tab_bar(cfg, "c", tag, tcounts)
    for n, ref in enumerate(refs, 1):
        h = chash(ref)
        row = [btn(str(n), f"cm:{tag}:{'t' if multi else 'i'}:{h}")]
        for m in CHAT_MODES:
            row.append(btn(("● " if modes[ref] == m else "") + MODE_LABEL[m], f"cm:{tag}:s:{m}:{h}"))
        if not slot:
            row.append(btn("Пр: " + PRIO_NAME[prios.get(ref)], f"cm:g:p:{h}"))
        row.append(btn("↺" if slot else "×", f"cm:{tag}:{'r' if slot else 'd'}:{h}"))
        kb.append(row)
    ctrl = [btn("Добавить", f"cm:{tag}:a")]
    if refs and not slot:
        ctrl.append(btn("Очистить вкладку" if (multi and cur != "*") else "Очистить всё", f"cm:{tag}:c"))
    kb.append(ctrl)
    kb.append([btn("Назад", f"sc:a:{slot}" if slot else "st:home")])
    return text, InlineKeyboardMarkup(inline_keyboard=kb)


def forget_chat(cfg, ref):
    """Чат удалён из общего списка — убираем его и из личных настроек аккаунтов, и из расписаний."""
    cfg["chat_modes"].pop(ref, None)
    (cfg.get("chat_priority") or {}).pop(ref, None)
    (cfg.get("chat_tabs") or {}).pop(ref, None)
    for acc in cfg["accounts"].values():
        (acc.get("chat_modes") or {}).pop(ref, None)
        for e in acc.get("schedule") or []:
            if e.get("chats") is not None:
                e["chats"] = [r for r in e["chats"] if r != ref]


async def chat_modes_button(call, tag, action, args):
    slot = None if tag == "g" else tag
    uid = call.from_user.id
    cfg = load_config()
    if slot and slot not in cfg["accounts"]:
        await call.answer("Такого аккаунта уже нет", show_alert=True)
        return
    refs = list(cfg["chat_modes"])
    toast = None
    if action == "a":
        waiting[uid] = f"addchat:{tag}:"
        await call.answer()
        await notify(call.message, "Отправьте <b>один</b> чат: ID, @юзернейм или ссылку.\nОтмена: /cancel")
        return
    if action == "t" and args:                       # перенос чата в следующую вкладку
        ref = ref_by_hash(refs, args[0])
        if ref:
            nxt = next_tab(cfg, tab_of_chat(cfg, ref))
            cfg.setdefault("chat_tabs", {})[ref] = nxt
            toast = f"→ {tab_name(cfg, nxt)}"
    if action == "i":
        ref = ref_by_hash(refs, args[0]) if args else None
        await call.answer(f"{chat_name_cache.get(ref) or ref}" if ref else "Чата уже нет", show_alert=True)
        return
    if action == "s" and len(args) == 2 and args[0] in CHAT_MODES:
        ref = ref_by_hash(refs, args[1])
        if ref:
            if slot:
                cfg["accounts"][slot].setdefault("chat_modes", {})[ref] = args[0]
            else:
                cfg["chat_modes"][ref] = args[0]
            toast = f"{MODE_LABEL[args[0]]}"
    elif action == "p" and not slot and args:         # приоритет по кругу: нет -> ЗП -> КП -> нет
        ref = ref_by_hash(refs, args[0])
        if ref:
            pri = cfg.setdefault("chat_priority", {})
            nxt = {None: "zp", "zp": "kp", "kp": None}[pri.get(ref) if pri.get(ref) in ("zp", "kp") else None]
            if nxt:
                pri[ref] = nxt
            else:
                pri.pop(ref, None)
            toast = "Приоритет: " + PRIO_NAME[nxt]
    elif action == "r" and slot and args:
        ref = ref_by_hash(refs, args[0])
        if ref:
            (cfg["accounts"][slot].get("chat_modes") or {}).pop(ref, None)
            toast = "Как в общем списке"
    elif action == "d" and not slot and args:
        ref = ref_by_hash(refs, args[0])
        if ref:
            forget_chat(cfg, ref)
            toast = "Удалено"
    elif action == "c" and not slot:
        for ref in tab_chats(cfg):                   # очищаем только открытую вкладку (на «Все» — всё)
            forget_chat(cfg, ref)
        toast = "Список очищен"
    save_config(cfg)
    await call.answer(toast)
    text, kb = chat_modes_view(slot)
    await show_pages(call, text, kb)


async def add_mode_chat(message, tag, raw, mode=None):
    """Добавить ОДИН чат. tag 'g' — в общий список (по умолчанию ОТКЛ), иначе — в общий список как ОТКЛ и
    сразу включить как ИСТ у этого аккаунта. mode задан командами /source (ИСТ) и /exclude (БС)."""
    refs = parse_refs(raw)
    if not refs:
        await notify(message, "Ошибка: Не понял чат. Отправьте ID, @юзернейм или ссылку t.me/…\nОтмена: /cancel")
        return False
    ref = refs[0]
    slot = None if tag == "g" else tag
    cfg = load_config()
    if slot and slot not in cfg["accounts"]:
        await notify(message, "Ошибка: Такого аккаунта уже нет")
        return True
    new = ref not in cfg["chat_modes"]
    if new:
        cfg["chat_modes"][ref] = mode if (mode and not slot) else "off"
        cfg.setdefault("chat_tabs", {})[ref] = cur_tab(cfg) if cur_tab(cfg) != "*" else cfg["tabs"][0]["id"]
    elif mode and not slot:
        cfg["chat_modes"][ref] = mode
    if slot:
        cfg["accounts"][slot].setdefault("chat_modes", {})[ref] = mode or "src"
    save_config(cfg)
    lines = []
    if new:
        async with working(message, "Проверяю чат…"):
            name = await lookup_chat_name(ref)
        lines.append(f"Добавлен: <b>{esc(name)}</b>" if name else f"Добавлен: <code>{esc(ref)}</code>")
        if not name:
            lines.append("Внимание: Ни один аккаунт пока не видит этот чат — проверьте ID и что аккаунт в нём состоит")
    else:
        lines.append("Этот чат уже был в списке — режим обновлён")
    shown = effective_modes(cfg, slot).get(ref, "off")
    lines.append(f"Режим: <b>{MODE_LABEL[shown]}</b>" + (" — выберите ИСТ или БС кнопками ниже" if shown == "off" else ""))
    if len(refs) > 1:
        lines.append("<i>Чаты добавляются по одному — взял первый, остальные отправьте отдельно.</i>")
    text, kb = chat_modes_view(slot)
    await send_pages(message, "\n".join(lines) + "\n\n" + text, kb)
    return True


@router.message(Command("chats", "source", "exclude"))
@admin
async def cmd_chat_modes(message: Message):
    name = message.text.split()[0].lstrip("/").split("@")[0].lower()
    mode = {"source": "src", "exclude": "bs"}.get(name)
    args = args_of(message)
    if args:                                  # /source @чат — добавить сразу
        await add_mode_chat(message, "g", " ".join(args), mode)
        return
    text, kb = chat_modes_view()
    await send_pages(message, text, kb)


# ---------------------------------------------------------
# Тексты и параметры (одним обработчиком)
# ---------------------------------------------------------

@router.message(Command(*SETTINGS))
@admin
async def cmd_setting(message: Message):
    name = message.text.split()[0].lstrip("/").split("@")[0]
    key, _kind, hint = SETTINGS[name]
    current = load_config()[key]
    waiting[message.from_user.id] = f"set:{name}"
    await notify(message, f"<b>{esc(hint)}</b>\n\n<b>Сейчас:</b>\n<code>{esc(current) if current != '' else 'не задано'}</code>\n\n"
                          "Отправьте новое значение.\nОтмена: /cancel")


@router.message(Command("dayreset"))
@admin
async def cmd_dayreset(message: Message):
    save_json(DAYLIMIT_FILE, {"day": day_key(), "uids": []})
    await notify(message, f"Счётчик ссылок за сегодня обнулён (лимит: {day_limit(load_config()) or 'нет'})")


@router.message(Command("auto", "dmtoggle"))
@admin
async def cmd_auto(message: Message):
    cfg = load_config()
    cfg["dm_reply_enabled"] = not cfg["dm_reply_enabled"]
    save_config(cfg)
    await notify(message, "Автоответы <b>включены</b>" if cfg["dm_reply_enabled"] else "Автоответы <b>выключены</b>")


def parse_setting(kind, text, current):
    if kind == "str":
        return text
    if kind == "int":
        value = int(text)
        if value <= 0:
            raise ValueError
        return value
    if kind == "int0":
        value = int(text)
        if value < 0:
            raise ValueError
        return value
    value = float(text.replace(",", "."))
    if value < 0:
        raise ValueError
    return value


# ---------------------------------------------------------
# Аккаунты: данные, вход, выход
# ---------------------------------------------------------

def save_account(cfg, slot, api_id, api_hash, phone_raw):
    """Возвращает (ошибка, предупреждение)."""
    phone = normalize_phone(phone_raw)
    if not api_id.isdigit() or not api_hash or not phone:
        return "Ошибка: Формат: api_id api_hash +79991234567", None
    acc = cfg["accounts"].setdefault(slot, dict(BLANK_ACCOUNT))
    acc.update(api_id=int(api_id), api_hash=api_hash, phone=phone)
    save_config(cfg)
    same = [s for s, a in cfg["accounts"].items() if s != slot and a.get("phone") == phone]
    return None, (f"Внимание: Этот номер уже указан у аккаунта {same[0]}." if same else None)


@router.message(Command("account"))
@admin
async def cmd_account(message: Message):
    uid = message.from_user.id
    args = args_of(message)
    if not args or not args[0].isdigit() or len(args) not in (1, 2, 4):
        await notify(message,
                     "<b>Использование</b>\n/account N — ввести данные по шагам\n"
                     "/account N api_id api_hash +79991234567\n"
                     "/account N +79991234567 — взять API у уже настроенного аккаунта")
        return
    slot = str(int(args[0]))
    cfg = load_config()
    if len(args) == 2:
        donor = next((a for s, a in sorted(cfg["accounts"].items(), key=lambda x: int(x[0]))
                      if s != slot and a["api_id"] and a["api_hash"]), None)
        if not donor:
            await notify(message, "Ошибка: Нет настроенного аккаунта, откуда взять API. Используйте полный формат.")
            return
        args = [args[0], str(donor["api_id"]), donor["api_hash"], args[1]]
    if len(args) == 4:
        err, warn = save_account(cfg, slot, args[1], args[2], args[3])
        if err:
            await notify(message, err)
            return
        await notify(message, f"{title(slot)} сохранён" + (f"\n{warn}" if warn else "")
                     + "\nКак войти?", login_kb(slot))
        return
    acc = cfg["accounts"].get(slot, BLANK_ACCOUNT)
    waiting[uid] = f"account:{slot}"
    await notify(message,
                 f"<b>{title(slot)}</b>\nAPI_ID: {acc['api_id'] or 'не задан'}\nТелефон: {esc(acc['phone'] or 'не задан')}\n\n"
                 "Введите: api_id api_hash +телефон\nИли /cancel")


@router.message(Command("logout"))
@admin
async def cmd_logout(message: Message):
    args = args_of(message)
    cfg = load_config()
    if not args or not args[0].isdigit():
        await notify(message, f"Использование: /logout N\nАккаунты: {', '.join(slots_sorted(cfg)) or 'нет'}")
        return
    slot = str(int(args[0]))
    if slot not in cfg["accounts"]:
        await notify(message, f"Ошибка: Аккаунта {slot} нет в списке.")
        return
    if run_locks:
        await notify(message, "Идёт рассылка — сначала остановите её: /stop")
        return
    await close_login(message.from_user.id)
    name = title(slot)
    await purge_account(slot)
    await notify(message, f"{name} — вышел и удалён из списка насовсем (сессия, личные чаты и расписания тоже).\n"
                          f"Вернуть: /account {slot}")


def login_kb(slot):
    return InlineKeyboardMarkup(inline_keyboard=[[btn("По номеру", f"lg:phone:{slot}"), btn("По QR", f"lg:qr:{slot}")]])


async def begin_login(message, uid, slot):
    acc = load_config()["accounts"][slot]
    if run_locks:
        await notify(message, "Идёт рассылка — сначала остановите её: /stop")
        return
    await close_login(uid)
    waiting.pop(uid, None)
    login[uid] = {"slot": slot, "step": "phone"}
    if acc["phone"]:
        await notify(message, f"{title(slot)}: отправляю код на {esc(acc['phone'])}…")
        await handle_login(message, uid, acc["phone"])
    else:
        await notify(message, f"<b>{title(slot)}</b>\nВведите номер телефона: +79991234567\n\nОтмена: /cancel")


@router.message(Command("login"))
@admin
async def cmd_login(message: Message):
    args = args_of(message)
    cfg = load_config()
    if not cfg["accounts"]:
        await notify(message, "Ошибка: Нет аккаунтов. Добавьте: /account 1")
        return
    if not args:
        rows = [[btn(f"{s} · " + strip_tags(title(s)), f"lg:pick:{s}")] for s in slots_sorted(cfg)]
        await notify(message, "<b>Какой аккаунт войти?</b>", InlineKeyboardMarkup(inline_keyboard=rows))
        return
    if args[0] not in cfg["accounts"]:
        await notify(message, f"Использование: /login N\nАккаунты: {', '.join(slots_sorted(cfg))}")
        return
    await ask_login_method(message, args[0])


async def ask_login_method(message, slot):
    acc = load_config()["accounts"][slot]
    if not acc["api_id"] or not acc["api_hash"]:
        await notify(message, f"Ошибка: Сначала /account {slot}")
        return
    await notify(message, f"<b>{title(slot)}</b>\nКак войти?", login_kb(slot))


async def login_button(call, parts):
    kind, slot = parts[0], parts[1]
    cfg = load_config()
    if slot not in cfg["accounts"]:
        await call.answer("Такого аккаунта уже нет", show_alert=True)
        return
    await call.answer()
    if kind == "pick":
        await ask_login_method(call.message, slot)
        return
    acc = cfg["accounts"][slot]
    if not acc["api_id"] or not acc["api_hash"]:
        await notify(call.message, f"Ошибка: Сначала /account {slot}")
        return
    if kind == "qr":
        await begin_qr_login(call.message, call.from_user.id, slot)
    else:
        await begin_login(call.message, call.from_user.id, slot)


async def close_login(uid):
    st = login.pop(uid, None)
    if not st:
        return
    if st.get("client"):
        with suppress(Exception):
            await st["client"].disconnect()
    with suppress(Exception):
        await get_client(st["slot"])  # аккаунт снова в пуле и слушает ЛС


def make_qr_png(url):
    """PNG с QR-кодом (нужна библиотека: pip install "qrcode[pil]")."""
    import qrcode
    buf = io.BytesIO()
    qrcode.make(url).save(buf, format="PNG")
    return buf.getvalue()


async def begin_qr_login(message, uid, slot):
    """Вход по QR: бот присылает картинку, в Telegram на телефоне: Настройки → Устройства → Подключить устройство.
    QR живёт ~30 сек — обновляется сам (до ~3 минут). Если включён 2FA, дальше бот попросит пароль."""
    cfg = load_config()
    acc = cfg["accounts"].get(slot) or {}
    if not acc.get("api_id") or not acc.get("api_hash"):
        await notify(message, f"Ошибка: Сначала /account {slot}")
        return
    if run_locks:
        await notify(message, "Идёт рассылка — сначала остановите её: /stop")
        return
    try:
        import qrcode  # noqa: F401
    except ImportError:
        await notify(message, 'Для QR нужна библиотека: <code>pip install "qrcode[pil]"</code> — установите и перезапустите бота.')
        return
    await close_login(uid)
    waiting.pop(uid, None)
    st = login[uid] = {"slot": slot, "step": "qr"}       # сразу занимаем слот, чтобы пул не создал второй клиент
    await drop_client(slot)
    try:
        client = st["client"] = create_client(slot)
        await asyncio.wait_for(client.connect(), CONNECT_TIMEOUT)
        if await client.is_user_authorized():
            await close_login(uid)
            await notify(message, f"{title(slot)} уже авторизован.")
            return
        qr = await client.qr_login()
    except Exception as e:
        if login.get(uid) is st:
            await close_login(uid)
        await notify(message, f"Ошибка: {esc(type(e).__name__)}: {esc(e)}")
        return
    spawn(qr_login_wait(message, uid, st, qr))


async def qr_login_wait(message, uid, st, qr):
    slot, client = st["slot"], st["client"]
    shown = None
    deadline = time.monotonic() + 180
    try:
        while login.get(uid) is st and time.monotonic() < deadline:
            png = await asyncio.to_thread(make_qr_png, qr.url)
            if shown is not None:
                with suppress(Exception):
                    await shown.delete()
            shown = await tg_call(lambda: message.answer_photo(
                BufferedInputFile(png, filename="qr.png"),
                caption=f"<b>{title(slot)}</b>: откройте Telegram на телефоне → Настройки → Устройства → "
                        "Подключить устройство → наведите камеру на QR.\nОбновляется сам. Отмена: /cancel",
                parse_mode="HTML"))
            try:
                await qr.wait(max(5, int(qr.expires.timestamp() - time.time()) if getattr(qr, "expires", None) else 30))
            except asyncio.TimeoutError:
                if login.get(uid) is not st:
                    return
                await qr.recreate()
                continue
            except SessionPasswordNeededError:
                if login.get(uid) is st:
                    st["step"] = "password"
                    await notify(message, "Введите пароль 2FA:")
                return
            if login.get(uid) is st:                       # вход выполнен
                await close_login(uid)
                await notify(message, f"Вход выполнен ({title(slot)}).")
            return
        if login.get(uid) is st:
            await close_login(uid)
            await notify(message, "QR не отсканировали вовремя. Повторите: /login " + str(slot))
    except Exception as e:
        if login.get(uid) is st:
            await close_login(uid)
            await notify(message, f"Ошибка QR-входа: {esc(type(e).__name__)}: {esc(e)}")
    finally:
        if shown is not None and login.get(uid) is not st:
            with suppress(Exception):
                await shown.delete()


async def handle_login(message, uid, text):
    st = login[uid]
    if st["step"] == "qr":
        await notify(message, "Ждём сканирования QR. Отмена: /cancel")
        return
    slot = st["slot"]
    cfg = load_config()

    if st["step"] == "phone":
        phone = normalize_phone(text)
        if not phone:
            await notify(message, "Ошибка: Неверный формат. Пример: +79991234567")
            return
        await drop_client(slot)  # освобождаем файл сессии на время входа
        try:
            client = st["client"] = create_client(slot)
            await client.connect()
            cfg["accounts"][slot]["phone"] = phone
            save_config(cfg)
            if await client.is_user_authorized():
                await close_login(uid)
                await notify(message, f"{title(slot)} уже авторизован.")
                return
            sent = await client.send_code_request(phone, force_sms=False)
            st.update(step="code", phone=phone, hash=sent.phone_code_hash)
            await notify(message, "Код отправлен. Введите его в формате <b>###.##</b>, например <code>123.45</code>")
        except FloodWaitError as e:
            await close_login(uid)
            await notify(message, f"Подождите {e.seconds} сек. и повторите вход.")
        except Exception as e:
            await close_login(uid)
            await notify(message, f"Ошибка: {esc(type(e).__name__)}: {esc(e)}")
        return

    client = st["client"]

    if st["step"] == "code":
        code = normalize_code(text)
        if not code:
            await notify(message, "Ошибка: Формат кода: <b>###.##</b>, например <code>123.45</code>")
            return
        try:
            await client.sign_in(phone=st["phone"], code=code, phone_code_hash=st["hash"])
            await close_login(uid)
            await notify(message, f"Вход выполнен ({title(slot)}).")
        except SessionPasswordNeededError:
            st["step"] = "password"
            await notify(message, "Введите пароль 2FA:")
        except PhoneCodeExpiredError:
            try:
                sent = await client.send_code_request(st["phone"], force_sms=False)
                st["hash"] = sent.phone_code_hash
                await notify(message, "Код истёк, отправил новый. Введите его (###.##):")
            except Exception as e:
                await close_login(uid)
                await notify(message, f"Ошибка: Не удалось отправить новый код: {esc(type(e).__name__)}")
        except PhoneCodeInvalidError:
            await notify(message, "Ошибка: Неверный код, введите ещё раз.")
        except FloodWaitError as e:
            await close_login(uid)
            await notify(message, f"Подождите {e.seconds} сек. и повторите вход.")
        except Exception as e:
            await close_login(uid)
            await notify(message, f"Ошибка входа: {esc(type(e).__name__)}: {esc(e)}")
        return

    if st["step"] == "password":
        try:
            await client.sign_in(password=text)
            await close_login(uid)
            await notify(message, f"Вход выполнен ({title(slot)}).")
        except Exception as e:
            if "password" in type(e).__name__.lower():
                await notify(message, "Ошибка: Неверный пароль 2FA, попробуйте ещё раз.")
            else:
                await close_login(uid)
                await notify(message, f"Ошибка 2FA: {esc(type(e).__name__)}: {esc(e)}")


# ---------------------------------------------------------
# /info — полная информация о человеке по всем аккаунтам
# ---------------------------------------------------------

async def admin_status(client, chat, entity):
    """('creator'|'admin'|None, должность). Если прямой запрос не прошёл — смотрим по списку админов."""
    try:
        perms = await retry(lambda: client.get_permissions(chat, entity))
        if perms is None:
            return None, None
        rank = getattr(getattr(perms, "participant", None), "rank", None)
        if getattr(perms, "is_creator", False):
            return "creator", rank
        if getattr(perms, "is_admin", False):
            return "admin", rank
        return None, None
    except FloodWaitError:
        raise
    except Exception:
        if entity.id in await fetch_admin_ids(client, chat):
            return "admin", None
        return None, None


async def resolve_user(client, target):
    try:
        entity = await retry(lambda: client.get_entity(target))
    except ValueError:
        await load_dialogs(client)  # подтянуть кэш диалогов и повторить
        entity = await retry(lambda: client.get_entity(target))
    if not isinstance(entity, User):
        raise RuntimeError("это не пользователь")
    return entity


def dm_state_name(v):
    m = re.fullmatch(r"(text[456])(?:x(\d+))?", v or "")
    if m:
        base = {"text4": "отказывался", "text5": "спрашивал", "text6": "спрашивал про контакт"}[m.group(1)]
        return base + (f" ×{m.group(2)}" if m.group(2) else "")
    return {"text1": "ждём ответ", "link": "ссылка выдана", "limited": "лимит на день (мест нет)",
            "done": "диалог закрыт", "manual": "ведёте сами"}.get(v, v)


async def profile_text(client, entity):
    """Карточка человека: всё, что есть. Пустые поля («о себе», «отметки») просто не показываются."""
    full = None
    with suppress(Exception):
        full = (await retry(lambda: client(functions.users.GetFullUserRequest(entity)))).full_user
    g = lambda obj, attr: getattr(obj, attr, None)

    name = " ".join(x for x in (entity.first_name, entity.last_name) if x) or "без имени"
    extra = [f"@{u.username}" for u in (g(entity, "usernames") or [])
             if g(u, "active") is not False and u.username and u.username != entity.username]
    uname = (f"@{entity.username}" if entity.username else "без юзернейма") + (f" (ещё: {', '.join(extra)})" if extra else "")
    lines = [
        f"<b>{esc(name)}</b>",
        f"{esc(uname)} · ID <code>{entity.id}</code>",
        "",
        f"Телефон: {esc('+' + entity.phone) if g(entity, 'phone') else 'скрыт'}",
        f"Статус: {esc(status_text(g(entity, 'status')))}",
    ]
    if g(full, "about"):
        lines.append(f"О себе: {esc(short(full.about, 300))}")
    bd = g(full, "birthday")
    if bd:
        lines.append(f"День рождения: {bd.day:02d}.{bd.month:02d}" + (f".{bd.year}" if g(bd, "year") else ""))
    if g(entity, "lang_code"):
        lines.append(f"Язык: {esc(entity.lang_code)}")
    counts = []
    with suppress(Exception):
        counts.append(f"Фото: {(await client.get_profile_photos(entity, limit=1)).total}")
    if g(full, "common_chats_count") is not None:
        counts.append(f"Общих чатов: {full.common_chats_count}")
    if counts:
        lines.append(" · ".join(counts))
    flags = [t for t, on in (
        ("премиум", g(entity, "premium")), ("бот", g(entity, "bot")), ("верифицирован", g(entity, "verified")),
        ("Внимание: скам", g(entity, "scam")), ("фейк", g(entity, "fake")), ("удалён", g(entity, "deleted")),
        ("ограничен", g(entity, "restricted")), ("в контактах", g(entity, "contact")),
    ) if on]
    if flags:
        lines.append(" · ".join(flags))
    reasons = [g(r, "text") or g(r, "reason") or "" for r in (g(entity, "restriction_reason") or [])]
    if any(reasons):
        lines.append("Ограничения: " + esc(short("; ".join(r for r in reasons if r), 200)))
    if g(full, "blocked"):
        lines.append("Заблокирован этим аккаунтом")
    return "\n".join(lines)


def split_text(text, limit=3800):
    """Режет длинный текст по строкам, чтобы влезло в сообщение Telegram.
    Если разрез попал внутрь <code>…</code>, тег закрывается и открывается заново — моно-текст не ломается."""
    chunks, cur, in_code = [], "", False
    for line in text.split("\n"):
        if cur and len(cur) + len(line) + 1 > limit:
            chunks.append(cur + ("</code>" if in_code else ""))
            cur = "<code>" if in_code else ""
        cur += ("\n" if cur else "") + line
        in_code = in_code ^ ((line.count("<code>") - line.count("</code>")) % 2 == 1)
    return chunks + ([cur] if cur else [])


@router.message(Command("info"))
@admin
@operation("Поиск человека")
async def cmd_info(message: Message):
    args = args_of(message)
    if not args:
        await notify(message, "Использование: /info 123456789 или /info @username")
        return
    raw = args[0].strip()
    target = int(raw) if re.fullmatch(r"-?\d+", raw) else re.sub(r"^(https?://)?t\.me/|^@", "", raw)

    cfg = load_config()
    slots = [sl for sl in slots_sorted(cfg) if session_exists(sl)]
    if not slots:
        await notify(message, "Ошибка: Нет авторизованных аккаунтов.")
        return
    tags = {str(r).lower(): "источник" for r in cfg["chat_source_groups"]}
    tags.update({str(r).lower(): "исключение" for r in cfg["chat_exclude_groups"]})

    box = {"profile": None, "entity": None}
    chats, per_acc, claimed = {}, {}, set()     # chats: id -> {"chat", "kind", "rank"}; админку каждого чата проверяем один раз
    sem = asyncio.Semaphore(4)

    async def check_admin(client, ch, entity, cid):
        async with sem:
            chats[cid]["kind"], chats[cid]["rank"] = await admin_status(client, ch, entity)

    async def work(slot):
        try:
            async with account_client(slot) as client:
                entity = await resolve_user(client, target)
                if box["entity"] is None:                         # карточку строит первый, кто нашёл человека
                    box["entity"] = entity
                    box["profile"] = await profile_text(client, entity)
                found = await common_chats(client, entity)
                jobs = []
                for ch in found:
                    cid = full_chat_id(ch)
                    chats.setdefault(cid, {"chat": ch, "kind": None, "rank": None})
                    if cid not in claimed:
                        claimed.add(cid)
                        jobs.append(check_admin(client, ch, entity, cid))
                await asyncio.gather(*jobs)
                per_acc[slot] = [full_chat_id(ch) for ch in found]
        except FloodWaitError as e:
            per_acc[slot] = f"FloodWait {e.seconds} сек"
        except ValueError:
            per_acc[slot] = "не видит этого человека"
        except Exception as e:
            per_acc[slot] = f"Внимание: {esc(err_text(e))}"

    async with working(message, "Ищу…"):
        await asyncio.gather(*(work(sl) for sl in slots))

    entity = box["entity"]
    parts = [box["profile"] or f"{esc(raw)}\nНи один аккаунт не смог найти человека."]
    if entity is not None:
        parts.append(person_block(entity.id, entity.username))
        parts.append(await prio_block(entity.id))

    def tag_of(cid):
        ch = chats[cid]["chat"]
        return tags.get(str(cid)) or tags.get(f"@{getattr(ch, 'username', '') or ''}".lower()) or ""

    def chat_name(cid):
        return esc(short(getattr(chats[cid]["chat"], "title", None) or "без названия", 45))

    admin_lines = []
    for cid, r in chats.items():
        if r["kind"]:
            role = "владелец" if r["kind"] == "creator" else "админ"
            admin_lines.append(f"• {chat_name(cid)} <code>{cid}</code> — {role}" + (f" «{esc(r['rank'])}»" if r["rank"] else "")
                               + (f" · {tag_of(cid)}" if tag_of(cid) else ""))
    if admin_lines:
        parts.append(f"<b>Админ в {len(admin_lines)} из {len(chats)} общих чатов</b>\n" + "\n".join(admin_lines))

    for slot in slots:                                  # по аккаунтам: только названия и ID (админы уже выше)
        head = f"<b>{title(slot)}</b>{role_mark(cfg, slot)}"
        res = per_acc.get(slot)
        if isinstance(res, str):
            parts.append(f"{head}: {res}")
        elif not res:
            parts.append(f"{head}: общих чатов нет")
        else:
            rows = [f"• {chat_name(cid)} <code>{cid}</code>" + (f" · {tag_of(cid)}" if tag_of(cid) else "") for cid in res]
            parts.append(f"{head} · общих чатов <b>{len(res)}</b>\n" + "\n".join(rows))

    for chunk in split_text("\n\n".join(parts)):
        await notify(message, chunk)


# ---------------------------------------------------------
# /stats — подробная статистика, сводка по человеку
# ---------------------------------------------------------

STATS_TZ = SPAM_TZ           # время в статистике — UTC+7 (как в расписании)
EVENT_KEEP_DAYS = 120        # журнал событий хранится 120 дней
_ev = {"list": None}

READ_LABELS = {"agreement": "согласие", "refusal": "отказ", "question": "вопрос", "source": "«откуда контакт?»",
               "stop": "просит не писать", "ack": "благодарность", "unclear": "непонятно", "media": "вложение",
               "manual": "ведёте диалог вы", "closed": "после закрытия диалога", "?": "сообщение"}


def _rewrite_events(rows):
    tmp = EVENTS_FILE + ".tmp"
    with open(tmp, "w", encoding="utf-8") as f:
        for e in rows:
            f.write(json.dumps(e, ensure_ascii=False) + "\n")
    os.replace(tmp, EVENTS_FILE)


def _seed_events():
    """Журнала ещё нет (первый запуск после обновления): восстанавливаем, что можно, из старых записей диалогов."""
    rows = []
    for k, meta in dm_meta.items():
        slot, uid = _split_key(k)
        if slot == "?" or not uid.lstrip("-").isdigit():
            continue
        st = dm_states.get(k) or ""
        ts = int(meta.get("ts") or 0)
        base = {"s": slot, "u": int(uid)}
        for key, val in (("n", meta.get("name")), ("c", meta.get("chat")), ("r", meta.get("ref"))):
            if val:
                base[key] = val
        rows.append({"t": ts, "k": "sent", **base})
        x = {"text4": "refusal", "text5": "question", "text6": "source", "link": "agreement"}.get(re.sub(r"x\d+$", "", st))
        if x or st in ("done", "manual"):
            rows.append({"t": ts, "k": "in", "x": x or "unclear", **base})
        if st == "link":
            rows.append({"t": ts, "k": "link", **base})
    return rows


def _events_load():
    rows, fresh = [], not os.path.exists(EVENTS_FILE)
    if not fresh:
        with suppress(OSError):
            with open(EVENTS_FILE, "r", encoding="utf-8") as f:
                for line in f:
                    with suppress(ValueError):
                        e = json.loads(line)
                        if isinstance(e, dict) and "k" in e:
                            rows.append(e)
    else:
        rows = _seed_events()
        with suppress(OSError):
            _rewrite_events(rows)
        return rows
    cutoff = time.time() - EVENT_KEEP_DAYS * 86400
    kept = [e for e in rows if not e.get("t") or e["t"] >= cutoff]
    if len(kept) != len(rows):
        with suppress(OSError):
            _rewrite_events(kept)
    return kept


def events_db():
    if _ev["list"] is None:
        _ev["list"] = _events_load()
    return _ev["list"]


def log_event(kind, slot=None, uid=None, name=None, chat=None, ref=None, **extra):
    """Одна запись журнала. kind: sent · fail · excl · found · in (ответ человека) · link · clean · out."""
    e = {"t": int(time.time()), "k": kind}
    if slot not in (None, ""):
        e["s"] = str(slot)
    if uid not in (None, ""):
        e["u"] = int(uid) if str(uid).lstrip("-").isdigit() else uid
    nm = str(name or "").lstrip("@").lower()
    if nm:
        e["n"] = nm
    if chat:
        e["c"] = chat
    if ref not in (None, ""):
        e["r"] = ref
    e.update({k: v for k, v in extra.items() if v is not None})
    events_db().append(e)
    try:
        with open(EVENTS_FILE, "a", encoding="utf-8") as f:
            f.write(json.dumps(e, ensure_ascii=False) + "\n")
    except OSError as ex:
        log.warning("журнал событий: %s", ex)


# ---- диалоги, собранные из журнала ----

def build_dialogs(evs=None):
    """События -> диалоги: [{slot, uid, name, chat, ref, sent, ins[(t, x)], link, cleaned}].
    sent=None — человек написал сам (например «я из анонки»). После «clean» следующая отправка — уже новый диалог."""
    evs = events_db() if evs is None else evs
    dialogs, active = [], {}

    def new(key, e, sent):
        d = {"slot": key[0], "uid": e.get("u"), "name": e.get("n"), "chat": e.get("c"), "ref": e.get("r"),
             "sent": sent, "ins": [], "link": None, "cleaned": None}
        dialogs.append(d)
        active[key] = d
        return d

    for e in sorted(evs, key=lambda e: e.get("t", 0)):
        k = e.get("k")
        if k not in ("sent", "in", "link", "clean"):
            continue
        key = (str(e.get("s")), e.get("u"))
        if k == "sent":
            new(key, e, e.get("t", 0))
            continue
        d = active.get(key) or new(key, e, None)
        if not d["name"] and e.get("n"):
            d["name"] = e["n"]
        if not d["chat"] and e.get("c"):
            d["chat"], d["ref"] = e["c"], e.get("r")
        if k == "in":
            d["ins"].append((e.get("t", 0), e.get("x") or "?"))
        elif k == "link":
            d["link"] = e.get("t", 0)
        else:
            d["cleaned"] = e.get("t", 0)
            active.pop(key, None)
    return dialogs


PERIODS = [("t", "Сегодня"), ("y", "Вчера"), ("7", "7 дней"), ("30", "30 дней"), ("a", "Всё")]


def period_range(p):
    now = datetime.now(STATS_TZ)
    mid = now.replace(hour=0, minute=0, second=0, microsecond=0)
    inf = float("inf")
    if p == "t":
        return mid.timestamp(), inf, "сегодня"
    if p == "y":
        return (mid - timedelta(days=1)).timestamp(), mid.timestamp(), "вчера"
    if p == "7":
        return (mid - timedelta(days=6)).timestamp(), inf, "7 дней"
    if p == "30":
        return (mid - timedelta(days=29)).timestamp(), inf, "30 дней"
    return 0, inf, "всё время"


def dialogs_in(p, ds=None):
    lo, hi, _ = period_range(p)
    ds = build_dialogs() if ds is None else ds
    return [d for d in ds if d["sent"] is not None and lo <= d["sent"] < hi]


def agg(ds):
    r = dict(sent=len(ds), replied=0, agreed=0, link=0, refusal=0, question=0, source=0, stop=0, cleaned=0, waiting=0)
    for d in ds:
        xs = {x for _, x in d["ins"]}
        if d["ins"]:
            r["replied"] += 1
        if "agreement" in xs or d["link"] is not None:
            r["agreed"] += 1
        if d["link"] is not None:
            r["link"] += 1
        for x in ("refusal", "question", "source", "stop"):
            if x in xs:
                r[x] += 1
        if d["cleaned"] is not None:
            r["cleaned"] += 1
        elif not d["ins"]:
            r["waiting"] += 1
    return r


def pct(a, b):
    return f"{a * 100 // b}%" if b else "-"


def mono(rows, left=1, gap=2):
    """Таблица моноширинным текстом: первые `left` колонок прижаты влево, остальные вправо."""
    widths = [max(len(str(r[i])) for r in rows) for i in range(len(rows[0]))]
    out = []
    for r in rows:
        cells = [str(c).ljust(w) if i < left else str(c).rjust(w) for i, (c, w) in enumerate(zip(r, widths))]
        out.append((" " * gap).join(cells).rstrip())
    return "<pre>" + esc("\n".join(out)) + "</pre>"


def hour_of(t):
    return datetime.fromtimestamp(t, STATS_TZ).hour


def hour_stats(ds):
    rows = [dict(sent=0, replied=0, agreed=0, inc=0) for _ in range(24)]
    for d in ds:
        xs = {x for _, x in d["ins"]}
        if d["sent"]:                                  # t=0 — старые записи без времени, в часы не попадают
            r = rows[hour_of(d["sent"])]
            r["sent"] += 1
            r["replied"] += 1 if d["ins"] else 0
            r["agreed"] += 1 if ("agreement" in xs or d["link"] is not None) else 0
        if d["ins"] and d["ins"][0][0]:
            rows[hour_of(d["ins"][0][0])]["inc"] += 1  # когда человек ответил (первый ответ)
    return rows


def acc_label(slot, n=10):
    info = acc_info.get(slot) or {}
    nm = ("@" + info["username"]) if info.get("username") else (info.get("name") or "")
    return f"{slot} {short(nm, n)}".strip()


def slot_key(s):
    return (not str(s).isdigit(), int(s) if str(s).isdigit() else 0)


def _evs(p):
    lo, hi, _ = period_range(p)
    return [e for e in events_db() if lo <= e.get("t", 0) < hi]


EMPTY = "<i>За этот период данных пока нет.</i>"
PRIO_NAME = {"zp": "ЗП", "kp": "КП", None: "-"}


# ---- приоритет чатов: ЗП / КП ----

def _nid(x):
    s = str(x).strip().lstrip("-")
    if s.isdigit():
        if s.startswith("100") and len(s) >= 12:
            s = s[3:]
        return s
    return None


def ref_matches(ref, gid=None, gtitle=None, uname=None):
    """Тот ли это чат, что записан в настройках под ref (ID, @юзернейм или ссылка)."""
    r = str(ref).strip()
    if gid is not None and str(gid).strip():
        if r.lower() == str(gid).strip().lower():
            return True
        a, b = _nid(r), _nid(gid)
        if a and b and a == b:
            return True
    if uname:
        u = re.sub(r"^(https?://)?(www\.)?t\.me/|^@", "", r, flags=re.I).strip("/").lower()
        if u and u == str(uname).lower():
            return True
    nm = chat_name_cache.get(r)
    if gtitle and nm and str(nm).strip().lower() == str(gtitle).strip().lower():
        return True
    return False


def chat_prio(cfg, gid=None, gtitle=None, uname=None):
    """'zp' / 'kp' / None — приоритет чата по настройкам (/chats). ЗП важнее КП."""
    best = None
    for ref, pr in (cfg.get("chat_priority") or {}).items():
        if pr in ("zp", "kp") and ref_matches(ref, gid, gtitle, uname):
            if pr == "zp":
                return "zp"
            best = best or pr
    return best


async def member_prios(cfg, uid):
    """В каких чатах с приоритетом состоит человек (по общим чатам наших аккаунтов): [(приоритет, название чата)]."""
    if not (cfg.get("chat_priority") or {}):
        return []
    found = {}

    async def one(slot):
        try:
            async with account_client(slot) as client:
                ent = await resolve_user(client, int(uid))
                for ch in await common_chats(client, ent):
                    pr = chat_prio(cfg, full_chat_id(ch), getattr(ch, "title", None), getattr(ch, "username", None))
                    if pr:
                        found[full_chat_id(ch)] = (pr, getattr(ch, "title", None) or str(full_chat_id(ch)))
        except Exception as e:
            log.info("приоритет: акк %s не проверил общие чаты: %s", slot, type(e).__name__)

    slots = [s for s in slots_sorted(cfg) if session_exists(s)]
    with suppress(Exception):
        await asyncio.wait_for(asyncio.gather(*(one(s) for s in slots)), 40)
    return list(found.values())


async def person_priority(cfg, uid, gid=None, gtitle=None):
    """-> ('zp'|'kp'|None, [основания]). ЗП, если человек состоит хотя бы в одном чате ЗП, даже если взяли его из другого."""
    reasons, got = [], []
    if gid is not None or gtitle:
        g = chat_prio(cfg, gid, gtitle)
        if g:
            got.append(g)
            reasons.append(f"группа входа ({esc(short(gtitle or str(gid), 30))}): {PRIO_NAME[g]}")
    for d in build_dialogs():
        if d["uid"] == uid and (d.get("ref") or d.get("chat")):
            pr = chat_prio(cfg, d.get("ref"), d.get("chat"))
            if pr:
                got.append(pr)
                reasons.append(f"чат-источник ({esc(short(d.get('chat') or str(d.get('ref')), 30))}): {PRIO_NAME[pr]}")
                break
    for pr, name in await member_prios(cfg, uid):
        got.append(pr)
        reasons.append(f"состоит в чате {esc(short(name, 30))}: {PRIO_NAME[pr]}")
    res = "zp" if "zp" in got else ("kp" if "kp" in got else None)
    return res, reasons


async def prio_block(uid, gid=None, gtitle=None):
    cfg = load_config()
    if not (cfg.get("chat_priority") or {}):
        return "Приоритет: не настроен (чаты ЗП / КП задаются в /chats)"
    pr, reasons = await person_priority(cfg, uid, gid, gtitle)
    head = f"Приоритет: <b>{PRIO_NAME[pr] if pr else 'не определён'}</b>"
    return head + ("".join("\n  - " + r for r in reasons) if reasons else "")


# ---- разделы статистики ----

def _joins(p=None):
    evs = events_db() if p is None else _evs(p)
    return [e for e in evs if e.get("k") == "join"]


def _ctx():
    """Общие данные для разделов: настройки, вступившие люди и их приоритет."""
    cfg = load_config()
    joined, jprio = set(), {}
    for e in events_db():
        if e.get("k") == "join" and e.get("u") is not None:
            joined.add(e["u"])
            if e.get("p"):
                jprio[e["u"]] = e["p"]
    return cfg, joined, jprio


def d_prio(d, cfg, jprio):
    return jprio.get(d["uid"]) or chat_prio(cfg, d.get("ref"), d.get("chat"))


def st_sum(p):
    evs = _evs(p)
    ds = dialogs_in(p)
    a = agg(ds)
    cfg, joined, _ = _ctx()
    lo, hi, _l = period_range(p)
    found = sum(int(e.get("n") or 0) for e in evs if e["k"] == "found")
    fails = Counter((e.get("w") or "?") for e in evs if e["k"] == "fail")
    n_excl = sum(1 for e in evs if e["k"] == "excl")
    inbound = sum(1 for d in build_dialogs() if d["sent"] is None and d["ins"] and lo <= d["ins"][0][0] < hi)
    if not ds and not evs:
        return EMPTY
    n_join = sum(1 for d in ds if d["uid"] in joined)
    S = a["sent"]
    funnel = [("Показатель", "Всего", "Доля"),
              ("Написано", S, "100%" if S else "-"),
              ("Ответили", a["replied"], pct(a["replied"], S)),
              ("Согласились", a["agreed"], pct(a["agreed"], S)),
              ("Ссылок выдано", a["link"], pct(a["link"], S)),
              ("Вступили в группу", n_join, pct(n_join, S))]
    react = [("Реакции", "Всего", "Доля"),
             ("Отказ", a["refusal"], pct(a["refusal"], S)),
             ("Вопрос", a["question"], pct(a["question"], S)),
             ("Откуда контакт", a["source"], pct(a["source"], S)),
             ("Просят не писать", a["stop"], pct(a["stop"], S)),
             ("Ждём ответ", a["waiting"], pct(a["waiting"], S)),
             ("Удалено без ответа", a["cleaned"], pct(a["cleaned"], S))]
    misc = [("Сбор и ошибки", "Всего")]
    if found:
        misc.append(("Найдено в чатах", found))
    misc.append(("Исключено (белый список)", n_excl))
    misc.append(("Ошибок отправки", sum(fails.values())))
    if inbound:
        misc.append(("Написали сами", inbound))
    out = ["<b>Воронка</b>", mono(funnel), "<b>Реакции</b>", mono(react), mono(misc)]
    if fails:
        out.append("Ошибки: " + esc(", ".join(f"{k} x{v}" for k, v in fails.most_common(3))))
    hs = hour_stats(ds)
    need = 5 if S >= 40 else 3
    cand = sorted((h for h in range(24) if hs[h]["sent"] >= need),
                  key=lambda h: (hs[h]["replied"] / hs[h]["sent"], hs[h]["sent"]), reverse=True)
    if cand:
        out.append("Лучшее время для отправки: " + ", ".join(f"{h:02d}:00 ({pct(hs[h]['replied'], hs[h]['sent'])})" for h in cand[:3]))
    return "\n".join(out)


def st_acc(p):
    evs = _evs(p)
    ds = dialogs_in(p)
    cfg, joined, _ = _ctx()
    by, fails = defaultdict(list), Counter(e.get("s") for e in evs if e["k"] == "fail")
    for d in ds:
        by[d["slot"]].append(d)
    slots = sorted(set(by) | {s for s in fails if s}, key=slot_key)
    if not slots:
        return EMPTY
    rows = [("Акк", "Напис", "Отв", "%", "Согл", "Ссыл", "Вст")]
    tot = dict(sent=0, replied=0, agreed=0, link=0, j=0)
    for s_ in slots:
        a = agg(by.get(s_, []))
        j = sum(1 for d in by.get(s_, []) if d["uid"] in joined)
        rows.append((acc_label(s_, 9), a["sent"], a["replied"], pct(a["replied"], a["sent"]), a["agreed"], a["link"], j))
        for k in ("sent", "replied", "agreed", "link"):
            tot[k] += a[k]
        tot["j"] += j
    rows.append(("Итого", tot["sent"], tot["replied"], pct(tot["replied"], tot["sent"]), tot["agreed"], tot["link"], tot["j"]))
    out = [mono(rows, gap=1), "<i>Напис - написано, Отв - ответили, Согл - согласились, Ссыл - ссылок, Вст - вступили</i>"]
    err = [f"{acc_label(s_, 14)}: {fails[s_]}" for s_ in slots if fails.get(s_)]
    if err:
        out.append("Ошибок отправки: " + esc("; ".join(err)))
    ranked = [s_ for s_ in slots if len(by.get(s_, [])) >= 5]
    if len(ranked) > 1:
        best = max(ranked, key=lambda s_: agg(by[s_])["replied"] / len(by[s_]))
        out.append(f"Лучший процент ответов: <b>{esc(acc_label(best, 14))}</b> ({pct(agg(by[best])['replied'], len(by[best]))})")
    return "\n".join(out)


def st_chat(p):
    evs = _evs(p)
    ds = dialogs_in(p)
    cfg, joined, jprio = _ctx()
    by = defaultdict(list)
    for d in ds:
        by[d["chat"] or "-"].append(d)
    found = Counter()
    for e in evs:
        if e["k"] == "found":
            found[e.get("c") or "-"] += int(e.get("n") or 0)
    chats = set(by) | set(found)
    if not chats:
        return EMPTY
    order = sorted(chats, key=lambda c: (len(by.get(c, [])), found.get(c, 0)), reverse=True)
    ref_of = {}
    for d in ds:
        ref_of.setdefault(d["chat"] or "-", d.get("ref"))
    rows = [("Группа", "Пр", "Собр", "Напис", "Отв", "%", "Согл", "Ссыл")]
    for c in order[:20]:
        a = agg(by.get(c, []))
        pr = chat_prio(cfg, ref_of.get(c), c if c != "-" else None)
        rows.append((short(c, 12), PRIO_NAME[pr], found.get(c, 0), a["sent"], a["replied"], pct(a["replied"], a["sent"]), a["agreed"], a["link"]))
    out = [mono(rows, gap=1),
           "<i>Пр - приоритет чата, Собр - собрано людей</i>"]
    if len(order) > 20:
        out.append(f"... и ещё групп: {len(order) - 20}")
    ranked = [c for c in order if len(by.get(c, [])) >= 5]
    if len(ranked) > 1:
        best = max(ranked, key=lambda c: agg(by[c])["replied"] / len(by[c]))
        worst = min(ranked, key=lambda c: agg(by[c])["replied"] / len(by[c]))
        if best != worst:
            out.append(f"Лучше всего отвечают: <b>{esc(short(best, 28))}</b> ({pct(agg(by[best])['replied'], len(by[best]))})")
            out.append(f"Хуже всего: <b>{esc(short(worst, 28))}</b> ({pct(agg(by[worst])['replied'], len(by[worst]))})")
    return "\n".join(out)


def st_prio(p):
    ds = dialogs_in(p)
    cfg, joined, jprio = _ctx()
    if not (cfg.get("chat_priority") or {}):
        return "<i>Приоритеты не заданы. В /chats у каждого чата есть кнопка «Пр»: ЗП / КП.</i>"
    if not ds:
        return EMPTY
    by = defaultdict(list)
    for d in ds:
        by[d_prio(d, cfg, jprio)].append(d)
    rows = [("Приоритет", "Напис", "Отв", "%", "Согл", "Ссыл", "Вст")]
    for key, name in (("zp", "ЗП"), ("kp", "КП"), (None, "Без")):
        g = by.get(key, [])
        a = agg(g)
        rows.append((name, a["sent"], a["replied"], pct(a["replied"], a["sent"]), a["agreed"], a["link"], sum(1 for d in g if d["uid"] in joined)))
    return ("\n".join(["<b>Люди по приоритету</b>", mono(rows, gap=1),
                       "<i>ЗП, если человек состоит в чате ЗП или вошёл в такую группу; иначе КП, если чат КП. "
                       "«Без» - приоритет не определён.</i>"]))


def st_join(p):
    js = _joins(p)
    cfg, joined, _ = _ctx()
    ds = dialogs_in(p)
    if not js:
        return ("<i>Вступлений за период нет. Перешлите боту уведомление #НОВЫЙ_ПОЛЬЗОВАТЕЛЬ - "
                "он запишет вход и сверит человека со своими записями.</i>")
    sent_uids = {d["uid"] for d in build_dialogs() if d["sent"] is not None}
    ours = [e for e in js if e.get("u") in sent_uids]
    link_uids = {d["uid"] for d in build_dialogs() if d["link"] is not None}
    got_link = [e for e in js if e.get("u") in link_uids]
    by_prio = Counter(PRIO_NAME[e.get("p")] for e in js)
    head = [("Вступления", "Всего"),
            ("Вошло в группы", len(js)),
            ("Из них мы писали", len(ours)),
            ("Из них получили ссылку", len(got_link)),
            ("Приглашал кто-то другой", len(js) - len(ours))]
    out = ["<b>Итоги</b>", mono(head),
           "Приоритет: " + ", ".join(f"{k} {v}" for k, v in sorted(by_prio.items()))]
    by = defaultdict(lambda: [0, 0])
    for e in js:
        c = e.get("c") or "-"
        by[c][0] += 1
        by[c][1] += 1 if e.get("u") in sent_uids else 0
    rows = [("Группа", "Вошло", "Наши")] + [(short(c, 22), v[0], v[1]) for c, v in sorted(by.items(), key=lambda x: -x[1][0])[:15]]
    out += ["<b>По группам</b>", mono(rows), "<i>Наши - те, кому писал бот</i>"]
    if ds:
        out.append(f"Из {len(ds)} написанных за период вступили: {sum(1 for d in ds if d['uid'] in joined)} "
                   f"({pct(sum(1 for d in ds if d['uid'] in joined), len(ds))})")
    return "\n".join(out)


def st_time(p):
    ds = dialogs_in(p)
    hs = hour_stats(ds)
    if not any(r["sent"] or r["inc"] for r in hs):
        return EMPTY
    out = []
    prow = [("Часть суток", "Напис", "Отв", "%", "Ответов")]
    for name, rg in (("Ночь 00-06", range(0, 6)), ("Утро 06-12", range(6, 12)), ("День 12-18", range(12, 18)), ("Вечер 18-24", range(18, 24))):
        s_ = sum(hs[h]["sent"] for h in rg)
        r_ = sum(hs[h]["replied"] for h in rg)
        prow.append((name, s_, r_, pct(r_, s_), sum(hs[h]["inc"] for h in rg)))
    out += ["<b>Части суток</b>", mono(prow, gap=1)]
    hrow = [("Час", "Напис", "Отв", "%", "Ответов")] + [
        (f"{h:02d}:00", hs[h]["sent"], hs[h]["replied"], pct(hs[h]["replied"], hs[h]["sent"]), hs[h]["inc"])
        for h in range(24) if hs[h]["sent"] or hs[h]["inc"]]
    out += ["<b>По часам</b>", mono(hrow, gap=1),
            "<i>Напис - сколько людей написали в этот час, Отв - сколько из них ответили, "
            "Ответов - сколько ответов пришло в этот час.</i>"]
    need = 5 if len(ds) >= 40 else 3
    rated = [h for h in range(24) if hs[h]["sent"] >= need]
    if rated:
        srt = sorted(rated, key=lambda h: (hs[h]["replied"] / hs[h]["sent"], hs[h]["sent"]), reverse=True)
        out.append("Лучшие часы для отправки: " + ", ".join(f"{h:02d}:00 ({pct(hs[h]['replied'], hs[h]['sent'])})" for h in srt[:3]))
        if len(srt) >= 4:
            out.append("Слабые часы: " + ", ".join(f"{h:02d}:00 ({pct(hs[h]['replied'], hs[h]['sent'])})" for h in srt[-3:][::-1]))
    if sum(r["inc"] for r in hs) >= 10:
        busy = sorted(range(24), key=lambda h: hs[h]["inc"], reverse=True)[:3]
        quiet = sorted(range(8, 24), key=lambda h: hs[h]["inc"])[:3]
        out.append("Прайм-тайм (больше всего ответов): " + ", ".join(f"{h:02d}:00" for h in sorted(busy)))
        out.append("Затишье (днём): " + ", ".join(f"{h:02d}:00" for h in sorted(quiet)))
    else:
        out.append("<i>Прайм-тайм и затишье появятся, когда наберётся хотя бы 10 ответов.</i>")
    wd = [dict(sent=0, replied=0, agreed=0) for _ in range(7)]
    for d in ds:
        if d["sent"]:
            w = datetime.fromtimestamp(d["sent"], STATS_TZ).weekday()
            wd[w]["sent"] += 1
            wd[w]["replied"] += 1 if d["ins"] else 0
            wd[w]["agreed"] += 1 if ({x for _, x in d["ins"]} & {"agreement"} or d["link"] is not None) else 0
    wrow = [("День", "Напис", "Отв", "%", "Согл")] + [
        (DAY_NAMES[i], r["sent"], r["replied"], pct(r["replied"], r["sent"]), r["agreed"]) for i, r in enumerate(wd) if r["sent"]]
    out += ["<b>По дням недели</b>", mono(wrow, gap=1)]
    return "\n".join(out)


def st_day(p):
    ds = [d for d in build_dialogs() if d["sent"]]
    today = datetime.now(STATS_TZ).date()
    by = defaultdict(list)
    for d in ds:
        by[datetime.fromtimestamp(d["sent"], STATS_TZ).date()].append(d)
    jn = Counter(datetime.fromtimestamp(e["t"], STATS_TZ).date() for e in _joins() if e.get("t"))
    rows = [("Дата", "Напис", "Отв", "Согл", "Ссыл", "Вход")]
    for i in range(14):
        x = today - timedelta(days=i)
        a = agg(by.get(x, []))
        if a["sent"] or jn.get(x):
            rows.append((f"{x.strftime('%d.%m')} {DAY_NAMES[x.weekday()]}", a["sent"], a["replied"], a["agreed"], a["link"], jn.get(x, 0)))
    if len(rows) == 1:
        return EMPTY
    return "<i>Последние 14 дней (выбранный период не влияет)</i>\n" + mono(rows, gap=1) + "\n<i>Вход - вступили в группы (по уведомлениям)</i>"


STAT_SECTIONS = [("sum", "Сводка", "сводка", st_sum), ("acc", "Аккаунты", "аккаунты", st_acc),
                 ("chat", "Группы", "группы", st_chat), ("prio", "Приоритет", "приоритет", st_prio),
                 ("join", "Вступления", "вступления", st_join), ("time", "Время", "время", st_time),
                 ("day", "Дни", "дни", st_day)]


def stats_text(sec, p):
    _lo, _hi, label = period_range(p)
    name, fn = next(((n, f) for k, _b, n, f in STAT_SECTIONS if k == sec), ("сводка", st_sum))
    head = f"<b>СТАТИСТИКА: {name.upper()}</b>" + ("" if sec == "day" else f" · {label}")
    text = f"{head}\n{LINE}\n" + fn(p)
    if len(text) > 4000:
        cut = text[:3900]
        text = cut[:cut.rfind("\n")] + ("</pre>" if cut.count("<pre>") > cut.count("</pre>") else "") + "\n..."
    return text


def stats_kb(sec, p):
    pr = [btn(("● " if k == p else "") + n, f"sv:{sec}:{k}") for k, n in PERIODS]
    sb = [btn(("● " if k == sec else "") + b, f"sv:{k}:{p}") for k, b, _n, _f in STAT_SECTIONS]
    return InlineKeyboardMarkup(inline_keyboard=[pr[:3], pr[3:], sb[:3], sb[3:6], sb[6:], [btn("Назад", "home")]])


@router.message(Command("stats"))
@admin
async def cmd_stats(message: Message):
    args = args_of(message)
    word = (args[0].lower() if args else "сегодня")
    p = {"сегодня": "t", "вчера": "y", "yesterday": "y", "неделя": "7", "7": "7", "месяц": "30", "30": "30",
         "всё": "a", "все": "a", "all": "a"}.get(word, "t")
    await notify(message, stats_text("sum", p), stats_kb("sum", p))


# ---- сводка по человеку: пришлите ID или @юзернейм ----

# ---- уведомления бота-журнала «#НОВЫЙ_ПОЛЬЗОВАТЕЛЬ»: перешлите их сюда ----

JOIN_TAG = "НОВЫЙ_ПОЛЬЗОВАТЕЛЬ"


def parse_join_notices(text):
    """Из пересланного текста достаёт все уведомления о входе: кто, группа, кто пригласил по ссылке, дата."""
    out = []
    for part in re.split(r"(?=#\s*НОВЫЙ_ПОЛЬЗОВАТЕЛЬ)", text or "", flags=re.I):
        if JOIN_TAG not in part.upper():
            continue

        def grab(label):
            m = re.search(label + r"\s*:\s*(.*?)\s*\[(-?\d+)\]", part, re.I)
            return (m.group(1).strip(), int(m.group(2))) if m else (None, None)

        who, uid = grab("Кто")
        gtitle, gid = grab("Группа")
        inv, inv_id = grab("По ссылке")
        if uid is None:
            m = re.search(r"#id\s*(\d+)", part, re.I)
            uid = int(m.group(1)) if m else None
        if uid is None:
            continue
        t = None
        m = re.search(r"Дата\s*:\s*(\d{1,2})\.(\d{1,2})\.(\d{2,4})\D+(\d{1,2}):(\d{2})(?::(\d{2}))?\s*(AM|PM)?", part, re.I)
        if m:
            with suppress(ValueError):
                d_, mo, y, h, mi, se, ap = m.groups()
                h = int(h)
                if ap:
                    h = h % 12 + (12 if ap.upper() == "PM" else 0)
                y = int(y) + (2000 if int(y) < 100 else 0)
                t = int(datetime(y, int(mo), int(d_), h, int(mi), int(se or 0), tzinfo=STATS_TZ).timestamp())
        out.append({"uid": uid, "who": who, "gid": gid, "gtitle": gtitle, "inv": inv, "inv_id": inv_id, "t": t})
    return out


async def handle_join_notice(message, text):
    items = parse_join_notices(text)
    if not items:
        return False
    cfg = load_config()
    mine = own_ids()
    for it in items[:10]:
        uid, gid = it["uid"], it["gid"]
        dup = any(e.get("k") == "join" and e.get("u") == uid and str(e.get("r")) == str(gid) for e in events_db())
        pr, reasons = await person_priority(cfg, uid, gid, it["gtitle"])
        if not dup:
            e = {"t": it["t"] or int(time.time()), "k": "join", "u": uid, "r": gid}
            for k, v in (("n", it["who"]), ("c", it["gtitle"]), ("inv", it["inv_id"]), ("invn", it["inv"]), ("p", pr)):
                if v:
                    e[k] = v
            events_db().append(e)
            with suppress(OSError):
                with open(EVENTS_FILE, "a", encoding="utf-8") as f:
                    f.write(json.dumps(e, ensure_ascii=False) + "\n")
        g_pr = chat_prio(cfg, gid, it["gtitle"])
        lines = ["<b>ВХОД В ГРУППУ</b>" + (" (повторное уведомление, уже учтено)" if dup else ""), LINE,
                 f"Человек: <b>{esc(it['who'] or 'без имени')}</b> · <code>{uid}</code>",
                 f"Группа: {esc(it['gtitle'] or '-')}" + (f" · <code>{gid}</code>" if gid else "")
                 + (f" · {PRIO_NAME[g_pr]}" if g_pr else ""),
                 "По ссылке: " + (f"{esc(it['inv'] or '-')} · <code>{it['inv_id']}</code>" if it["inv_id"] else "-")
                 + (" (наш аккаунт)" if it["inv_id"] in mine else ""),
                 f"Время: {fmt_ts(it['t'] or int(time.time()))}", "",
                 person_block(uid, None), "",
                 f"Приоритет: <b>{PRIO_NAME[pr] if pr else 'не определён'}</b>"
                 + ("".join("\n  - " + r for r in reasons) if reasons else
                    ("" if cfg.get("chat_priority") else " (приоритеты чатов не заданы: /chats)"))]
        await notify(message, "\n".join(lines), reply=True)
    return True


def parse_person_ref(text):
    """-> (uid, username, явно_ли_это_ссылка_на_человека) или None."""
    t = re.sub(r"^(https?://)?(www\.)?t\.me/", "", text.strip()).strip("/")
    if re.fullmatch(r"-?\d{5,}", t):
        return int(t), None, True
    m = re.fullmatch(r"(@?)([A-Za-z][A-Za-z0-9_]{3,31})", t)
    if m:
        return None, m.group(2).lower(), bool(m.group(1)) or text.strip().lower().startswith(("t.me/", "http"))
    return None


def fmt_ts(t):
    return datetime.fromtimestamp(t, STATS_TZ).strftime("%d.%m %H:%M") if t else "время неизвестно (до обновления)"


def person_block(uid=None, uname=None):
    """Короткая сводка по человеку по ВСЕМ аккаунтам: приглашали ли, с какого аккаунта, когда, из какого чата, просил ли ссылку."""
    uname = (uname or "").lstrip("@").lower() or None
    ds = build_dialogs()
    if uid is None and uname:
        uid = next((d["uid"] for d in ds if d["name"] == uname and d["uid"]), None)
    mine = [d for d in ds if (uid is not None and d["uid"] == uid) or (uname and d["name"] == uname)]
    if not mine:
        if uname and uname in read_processed():
            return "<b>Приглашали:</b> да \n<i>аккаунт, чат и время неизвестны — запись сделана до обновления</i>"
        return "<b>Приглашали:</b> нет — в записях бота этого человека нет"
    invited = any(d["sent"] is not None for d in mine)
    mine.sort(key=lambda d: d["sent"] if d["sent"] is not None else (d["ins"][0][0] if d["ins"] else 0), reverse=True)
    lines = [f"<b>Приглашали:</b> {'да ' if invited else 'нет — человек написал сам'}"]
    for d in mine[:4]:
        xs = [x for _, x in d["ins"]]
        asked = "agreement" in xs or d["link"] is not None
        lines += ["", f"<b>{title(d['slot'])}</b>"]
        if d["sent"] is not None:
            lines.append(f"Написали: {fmt_ts(d['sent'])}")
        else:
            lines.append(f"Написал сам: {fmt_ts(d['ins'][0][0] if d['ins'] else 0)}")
        if d["chat"]:
            lines.append(f"Из чата: {esc(d['chat'])}" + (f" (<code>{d['ref']}</code>)" if d.get("ref") else ""))
        if d["ins"]:
            t0 = d["ins"][0][0]
            gap = (f" (через {fmt_left(t0 - d['sent'])})" if t0 - d["sent"] >= 60 else " (сразу)") if d["sent"] and t0 and t0 >= d["sent"] else ""
            seen = []
            for x in xs:
                lb = READ_LABELS.get(x, x)
                if lb not in seen:
                    seen.append(lb)
            lines.append(f"Ответил: {fmt_ts(t0)}{gap} — {esc(', '.join(seen))}")
        elif d["cleaned"] is not None:
            lines.append(f"Не ответил — диалог удалён ({fmt_ts(d['cleaned'])})")
        else:
            lines.append("Пока не ответил")
        link = f"Просил ссылку: {'да' if asked else 'нет'}"
        if d["link"] is not None:
            link += f" · выдана {fmt_ts(d['link'])}"
        elif asked:
            link += " · ссылка не ушла"
        lines.append(link)
        st = dm_get(d["slot"], d["uid"]) if d["uid"] else None
        if st:
            lines.append(f"Диалог: {esc(dm_state_name(st))}")
    if len(mine) > 4:
        lines.append(f"\n<i>… и ещё записей: {len(mine) - 4}</i>")
    return "\n".join(lines)


async def person_summary(uid=None, uname=None):
    uname = (uname or "").lstrip("@").lower() or None
    if not uid and uname:
        uid = next((d["uid"] for d in build_dialogs() if d["name"] == uname and d["uid"]), None)
    who = (f"@{uname}" if uname else "") + (f" · <code>{uid}</code>" if uid else "")
    text = f"<b>СВОДКА</b>\n{LINE}\n{who}\n\n" + person_block(uid, uname)
    if uid:
        text += "\n\n" + await prio_block(uid)
    return text


# ---------------------------------------------------------
# /admin_list и /scan_group
# ---------------------------------------------------------

@router.message(Command("admin_list"))
@admin
@operation("Список админов")
async def cmd_admin_list(message: Message):
    args = args_of(message)
    if not args:
        await notify(message, "Использование: /admin_list -1001234567890 (ID, @юзернейм или ссылка на чат)")
        return
    ref = normalize_ref(args[0])

    async def job(client, entity, slot):
        return entity, await fetch_admins(client, entity, strict=True)

    async with working(message, "Ищу…"):
        slot, (entity, admins) = await with_chat_access(ref, job)
    label, _ = chat_names(entity, ref)
    admins.sort(key=lambda a: (not a["creator"], a["username"] or "~", a["id"]))
    bots = sum(1 for a in admins if a["bot"])
    head = f"<b>Админы</b> · {esc(label)}\nчерез {title(slot)} · всего <b>{len(admins)}</b>" + (f" (ботов {bots})" if bots else "")
    if not admins:
        await notify(message, head + "\n\nСписок админов пуст или недоступен.")
        return

    def icon(a):
        return "владелец" if a["creator"] else "бот" if a["bot"] else "админ"

    if len(admins) <= 40:
        lines = [f"{icon(a)} {('@' + a['username']) if a['username'] else '—'} | <code>{a['id']}</code>"
                 + (f" | {esc(a['name'])}" if a["name"] else "") + (f" · «{esc(a['rank'])}»" if a["rank"] else "")
                 for a in admins]
        await notify(message, head + "\n\n" + "\n".join(lines))
        return
    data = align_cols([(('@' + a['username']) if a['username'] else '—', str(a['id']), a['name'] or '', a['rank'] or '') for a in admins])
    await message.answer_document(BufferedInputFile(data.encode("utf-8"), filename=f"admins_{ref}.txt"),
                                  caption=head, parse_mode="HTML")


@router.message(Command("scan_group"))
@admin
@operation("Скан группы")
async def cmd_scan_group(message: Message):
    args = args_of(message)
    if not args:
        await notify(message, "Использование: /scan_group -1001234567890 [сколько сообщений]\nБез числа берётся значение из /scan.")
        return
    cfg = load_config()
    ref = normalize_ref(args[0])
    limit = int(args[1]) if len(args) > 1 and args[1].isdigit() and int(args[1]) > 0 else int(cfg["scan_messages_limit"])

    async def job(client, entity, slot):
        admin_ids_chat = await fetch_admin_ids(client, entity)
        users, stats = {}, {"admins": 0, "nouser": 0}

        def handle(msg, sender):
            if not isinstance(sender, User) or sender.id in users or sender.bot or sender.deleted:
                return
            if sender.id in admin_ids_chat:
                stats["admins"] += 1
                return
            if not sender.username:
                stats["nouser"] += 1
                return
            users[sender.id] = sender.username

        seen, partial = await scan_messages(client, entity, limit, handle)
        return entity, users, stats, seen, partial

    async with working(message, "Ищу…"):
        slot, (entity, users, stats, seen, partial) = await with_chat_access(ref, job)
    label, _ = chat_names(entity, ref)
    if not users:
        await notify(message, f"<b>{esc(label)}</b>\nПросмотрено {seen} сообщений — подходящих людей не нашёл.")
        return
    rows = sorted(users.items(), key=lambda x: x[1].lower())
    data = align_cols([(f"@{uname}", str(uid)) for uid, uname in rows])
    caption = (f"<b>{esc(label)}</b>\nчерез {title(slot)} · просмотрено {seen} сообщ."
               + (" неполно (сбой Telegram)" if partial else "") + "\n"
               f"людей: <b>{len(rows)}</b> · админов пропущено: {stats['admins']} · без юзернейма: {stats['nouser']}")
    await message.answer_document(BufferedInputFile(data.encode("utf-8"), filename=f"scan_{ref}.txt"),
                                  caption=caption, parse_mode="HTML")


# ---------------------------------------------------------
# Запуск
# ---------------------------------------------------------

# ВАЖНО: обработчик обычного текста должен регистрироваться ПОСЛЕДНИМ — иначе он перехватывает
# все сообщения раньше команд, объявленных ниже него, и те «не реагируют».
@router.message(F.text, ~F.text.startswith("/"))
async def handle_input(message: Message):
    uid = message.from_user.id
    if uid not in admin_ids or message.text.startswith("/"):
        return
    text = message.text.strip()

    if uid in login:
        await handle_login(message, uid, text)
        return

    if JOIN_TAG in text.upper() and await handle_join_notice(message, text):
        return

    # ответ человеку из бота: реплаем на уведомление или после кнопки «✍️ Ответить»
    target = None
    reply_to = getattr(message, "reply_to_message", None)
    if reply_to is not None:
        target = reply_map.get(f"{message.chat.id}:{reply_to.message_id}")
    state = waiting.get(uid)
    if target is None and state and state.startswith("dmreply:"):
        target = state.split(":", 1)[1]
        waiting.pop(uid, None)
    if target:
        slot, user_id = target.split(":")
        try:
            await dm_send(slot, user_id, text)
        except Exception as e:
            await notify(message, f"Ошибка: Не отправилось ({title(slot)}): {esc(type(e).__name__)}: {esc(e)}")
            return
        set_dm_state(slot, user_id, "manual")   # дальше диалог ведёте вы: автоответов не будет
        await notify(message, f"Отправлено · {title(slot)} → <code>{user_id}</code>")
        return

    if not state:
        ref = parse_person_ref(text)
        if ref and (ref[2] or ref[0] is not None):       # ID или @юзер/t.me-ссылка; голое слово без @ не трогаем
            await notify(message, await person_summary(ref[0], ref[1]) + "\n\n<i>Полный профиль и общие чаты: /info</i>", reply=True)
        return
    cfg = load_config()

    if state.startswith("addchat:"):        # чат в общий список / аккаунту — строго по одному
        _, tag, mode = state.split(":", 2)
        if await add_mode_chat(message, tag, text, mode or None):
            waiting.pop(uid, None)
        return

    if state.startswith(("tabadd:", "tabren:")):     # название вкладки
        parts = state.split(":")
        name = text.strip()[:24]
        if not name:
            await notify(message, "Ошибка: Пустое название. Отправьте ещё раз или /cancel")
            return
        if parts[0] == "tabadd":
            if len(cfg["tabs"]) >= MAX_TABS:
                waiting.pop(uid, None)
                await notify(message, f"Ошибка: Максимум вкладок: {MAX_TABS}")
                return
            tid = new_tab_id(cfg)
            cfg["tabs"].append({"id": tid, "name": name})
            ui_tab["id"] = tid
        else:
            for t in cfg["tabs"]:
                if t["id"] == parts[3]:
                    t["name"] = name
        save_config(cfg)
        waiting.pop(uid, None)
        view = render_section(parts[1], parts[2])
        done = f"Вкладка «{esc(name)}» сохранена"
        if view:
            await send_pages(message, done + "\n\n" + view[0], view[1])
        else:
            await notify(message, done)
        return

    if state.startswith("addtext:"):        # текст в список
        kind = state.split(":", 1)[1]
        if kind in TEXT_LISTS:
            if await add_text(message, kind, text):
                waiting.pop(uid, None)
        return

    if state.startswith("account:"):
        slot = state.split(":", 1)[1]
        parts = text.split()
        err, warn = save_account(cfg, slot, *parts) if len(parts) == 3 else ("Ошибка: Формат: api_id api_hash +79991234567", None)
        if err:
            await notify(message, err)
            return
        waiting.pop(uid, None)
        await notify(message, f"{title(slot)} сохранён" + (f"\n{warn}" if warn else "")
                     + "\nКак войти?", login_kb(slot))
        return

    key, kind, _ = SETTINGS[state.split(":", 1)[1]]
    try:
        cfg[key] = parse_setting(kind, text, cfg[key])
    except ValueError:
        await notify(message, "Ошибка: Неверное значение, попробуйте ещё раз или /cancel.")
        return
    save_config(cfg)
    waiting.pop(uid, None)
    await notify(message, f"Сохранено:\n<code>{esc(short(cfg[key], 300)) if cfg[key] != '' else 'пусто'}</code>")


# ---------------------------------------------------------
# Тексты: списки с кнопками «добавить / убрать» (/text, /text2, /text3, /text4)
# ---------------------------------------------------------

TEXT_LISTS = {
    "text": ("messages", "Первое сообщение", "один текст: уходит каждому новому человеку"),
    "text2": ("texts_link", "Текст со ссылкой",
              "один текст: уходит, когда человек согласился. Сюда вставьте пригласительную ссылку t.me/+… — "
              "бот сам проверит, что она не истекла, и сообщит вам, что человек, возможно, зайдёт"),
    "text3": ("texts_refusal", "Ошибка: Ответы на отказ", "по порядку: на 1-й отказ — 1-й текст, на 2-й — 2-й и т.д."),
    "text4": ("texts_question", "Ответы на вопрос и сомнение", "по порядку: на каждый следующий вопрос — следующий текст"),
    "text5": ("texts_source", "Ответы на «откуда мой контакт?»", "по порядку: на каждый следующий такой вопрос — следующий текст"),
    "text6": ("texts_limit", "Текст при лимите на день",
              "один текст: уходит вместо ссылки, когда за сегодня ссылку уже получило максимум людей (лимит — /daylimit)"),
}
SINGLE_TEXTS = {"text", "text2", "text6"}      # здесь ровно один текст: новый заменяет старый, без добавления
PLACEHOLDER_HINT = "<i>В тексте можно: {chat} — чат, где нашли человека, {name} — его имя</i>"


def text_list_view(kind):
    """Тексты показываются ПОЛНОСТЬЮ (длинные режутся на несколько сообщений при отправке)."""
    key, head, hint = TEXT_LISTS[kind]
    items = [str(t) for t in (load_config().get(key) or [])]
    if kind in SINGLE_TEXTS:
        extra = f"\n<i>В старом списке было {len(items)} вариантов — используется только первый.</i>" if len(items) > 1 else ""
        text = (f"<b>{head}</b>\n<i>{hint}</i>\n{PLACEHOLDER_HINT}{extra}\n\n"
                + (f"<code>{esc(items[0])}</code>" if items else "<i>не задан</i>"))
        ctrl = [btn("Изменить", f"tx:{kind}:add")] + ([btn("Удалить", f"tx:{kind}:clear")] if items else [])
        return text, InlineKeyboardMarkup(inline_keyboard=[ctrl, [btn("Назад", "st:texts")]])
    rows = [f"<b>{n}.</b>\n<code>{esc(t)}</code>" for n, t in enumerate(items, 1)]
    text = (f"<b>{head}</b> ({len(items)})\n<i>{hint}</i>\n{PLACEHOLDER_HINT}\n"
            "<i>Нажмите на текст — он скопируется.</i>\n\n"
            + ("\n\n".join(rows) if rows else "<i>пока пусто</i>"))
    dels = [btn(f"× {n}", f"tx:{kind}:del:{n - 1}") for n in range(1, len(items) + 1)]
    kb = [dels[i:i + 5] for i in range(0, len(dels), 5)]
    ctrl = [btn("Добавить", f"tx:{kind}:add")]
    if items:
        ctrl.append(btn("Очистить всё", f"tx:{kind}:clear"))
    kb.append(ctrl)
    kb.append([btn("Назад", "st:texts")])
    return text, InlineKeyboardMarkup(inline_keyboard=kb)


async def add_text(message, kind, raw):
    """/text — один текст (новый заменяет старый). Остальные списки: добавляет; строка «---» режет на несколько. True — готово."""
    key = TEXT_LISTS[kind][0]
    cfg = load_config()
    if kind in SINGLE_TEXTS:
        new = raw.strip()
        if not new:
            await notify(message, "Ошибка: Пустой текст. Отправьте текст ещё раз или /cancel")
            return False
        cfg[key] = [new]
        done = "Текст заменён"
    else:
        added = split_variants(raw) or ([raw.strip()] if raw.strip() else [])
        if not added:
            await notify(message, "Ошибка: Пустой текст. Отправьте текст ещё раз или /cancel")
            return False
        cfg[key] = list(cfg.get(key) or []) + added
        done = f"Добавлено: {len(added)}"
    save_config(cfg)
    if kind == "text2":                      # сразу проверяем, действует ли ссылка
        client = any_client()
        if client is None:
            done += "\nВнимание: Ни один аккаунт не подключён — ссылку проверить не смог"
        else:
            lk, nm = await check_invite(client, cfg[key][0])
            done += {"ok": "\nСсылка действует " + (f" · {esc(nm)}" if nm else ""),
                     "expired": "\nВнимание: <b>Ссылка уже недействительна</b> — пришлите новую",
                     "none": "\nПригласительной ссылки t.me/+… в тексте нет — срок проверять нечего",
                     "error": "\nВнимание: Не удалось проверить ссылку (сбой связи)"}[lk]
    text, kb = text_list_view(kind)
    await send_pages(message, f"{done}\n\n" + text, kb)
    return True


async def text_button(call, kind, action, arg=None):
    key = TEXT_LISTS[kind][0]
    if action == "add":
        waiting[call.from_user.id] = f"addtext:{kind}"
        await call.answer()
        await notify(call.message, "Отправьте новый текст одним сообщением — он заменит текущий.\nОтмена: /cancel"
                     if kind in SINGLE_TEXTS else "Отправьте новый текст одним сообщением.\nОтмена: /cancel")
        return
    cfg = load_config()
    items = list(cfg.get(key) or [])
    toast = None
    if action == "clear":
        items, toast = [], "Удалено" if kind in SINGLE_TEXTS else "Список очищен"
    elif action == "del" and arg is not None and arg.isdigit() and int(arg) < len(items):
        items.pop(int(arg))
        toast = "Удалено"
    cfg[key] = items[:1] if kind in SINGLE_TEXTS else items
    save_config(cfg)
    await call.answer(toast)
    text, kb = text_list_view(kind)
    await show_pages(call, text, kb)


@router.message(Command(*TEXT_LISTS))
@admin
async def cmd_texts(message: Message):
    kind = message.text.split()[0].lstrip("/").split("@")[0].lower()
    parts = message.text.split(None, 1)
    if len(parts) > 1:                       # /text Привет! — добавить (для /text — заменить) сразу
        await add_text(message, kind, parts[1])
        return
    text, kb = text_list_view(kind)
    await send_pages(message, text, kb)


# ---------------------------------------------------------
# Файлы-столбики
# ---------------------------------------------------------

def align_cols(rows):
    """Строки-кортежи -> текст в столбик (колонки выровнены, перенос \r\n — читается и в Блокноте)."""
    if not rows:
        return ""
    widths = [max(len(str(r[i])) for r in rows) for i in range(len(rows[0]) - 1)]
    out = []
    for r in rows:
        cells = [str(c).ljust(w) for c, w in zip(r, widths)] + [str(r[-1])]
        out.append("  ".join(cells).rstrip())
    return "\r\n".join(out)


# ---------------------------------------------------------
# Ссылка-приглашение (проверка срока) и очистка диалогов без ответа
# ---------------------------------------------------------

def own_ids():
    return {int(i["id"]) for i in acc_info.values() if i.get("id")}


INVITE_RE = re.compile(r"(?:https?://)?(?:www\.)?(?:t|telegram)\.me/(?:\+|joinchat/)([A-Za-z0-9_-]{8,})", re.I)
INVITE_DEAD = tuple(
    getattr(tl_errors, name)
    for name in ("InviteHashExpiredError", "InviteHashInvalidError", "InviteHashEmptyError")
    if hasattr(tl_errors, name)
)
_link_cache = {}


async def check_invite(client, text):
    """Действует ли пригласительная ссылка из текста: -> (статус, название группы).
    статус: ok — действует · expired — истекла/отозвана · none — в тексте нет пригласительной ссылки · error — не удалось проверить."""
    m = INVITE_RE.search(str(text or ""))
    if not m:
        return "none", ""
    h = m.group(1)
    hit = _link_cache.get(h)
    if hit and time.time() - hit[0] < 120:
        return hit[1], hit[2]
    status, name = "error", ""
    try:
        res = await asyncio.wait_for(client(functions.messages.CheckChatInviteRequest(h)), 25)
        status = "ok"
        name = getattr(res, "title", None) or getattr(getattr(res, "chat", None), "title", None) or ""
    except INVITE_DEAD:
        status = "expired"
    except FloodWaitError:
        pass
    except Exception as e:
        log.warning("проверка ссылки: %s: %s", type(e).__name__, e)
    if status != "error":
        if len(_link_cache) > 200:
            _link_cache.clear()
        _link_cache[h] = (time.time(), status, name)
    return status, name


def day_key():
    return datetime.now(SPAM_TZ).strftime("%Y-%m-%d")     # «день» считаем по UTC+7, как расписание


def day_links():
    st = load_json(DAYLIMIT_FILE, {})
    if st.get("day") != day_key() or not isinstance(st.get("uids"), list):
        st = {"day": day_key(), "uids": []}
    return st


def day_limit(cfg):
    return max(0, int(cfg.get("daily_link_limit") or 0))


def day_used():
    return len(day_links()["uids"])


def day_is_full(cfg, uid):
    lim = day_limit(cfg)
    st = day_links()
    return bool(lim) and str(uid) not in st["uids"] and len(st["uids"]) >= lim


def day_reserve(cfg, uid):
    """Занять место за человеком. True — место есть; False — лимит исчерпан.
    Внутри нет await: два человека одновременно не смогут занять одно и то же последнее место."""
    st = day_links()
    uid = str(uid)
    if uid in st["uids"]:
        return True
    lim = day_limit(cfg)
    if lim and len(st["uids"]) >= lim:
        return False
    st["uids"].append(uid)
    save_json(DAYLIMIT_FILE, st)
    return True


def day_release(uid):
    st = day_links()
    uid = str(uid)
    if uid in st["uids"]:
        st["uids"].remove(uid)
        save_json(DAYLIMIT_FILE, st)


def day_line(cfg):
    lim = day_limit(cfg)
    return f"{day_used()} из {lim}" if lim else f"{day_used()} (без лимита)"


def limit_text_of(cfg):
    """Текст для тех, кому не хватило места на сегодня (/text6) или пустая строка."""
    return next((str(t).strip() for t in (cfg.get("texts_limit") or []) if str(t).strip()), "")


def link_text_of(cfg):
    """Текст со ссылкой (/text2) или пустая строка."""
    return next((str(t).strip() for t in (cfg.get("texts_link") or []) if str(t).strip()), "")


def any_client():
    for c in list(pool.values()):
        if c is not None and c.is_connected():
            return c
    return None


def mark_replied(slot, uid):
    """Человек ответил — он больше не «молчун», его диалог не будет удалён."""
    meta = dm_meta.get(f"{slot}:{uid}")
    if meta is not None and not meta.get("replied"):
        meta["replied"] = True
        save_json(DM_META_FILE, dm_meta)


NOREPLY_POLL = 600   # сек между проверками «кто не ответил»


async def cleanup_once():
    """Кому писали, но ответа нет дольше /wait часов: диалог удаляется у обоих, человек снова «не писали» — ему можно написать заново."""
    hours = float(load_config().get("noreply_hours") or 0)
    if hours <= 0:
        return
    now = time.time()
    due = []
    for k, st in list(dm_states.items()):
        slot, uid = _split_key(k)
        meta = dm_meta.get(k) or {}
        if st != "text1" or slot == "?" or meta.get("replied") or not meta.get("ts"):
            continue
        if now - float(meta["ts"]) >= hours * 3600:
            due.append((slot, uid, meta.get("name")))
    cleaned = 0
    for slot, uid, name in due:
        async with dm_lock(slot, uid):
            k = f"{slot}:{uid}"
            if dm_states.get(k) != "text1" or (dm_meta.get(k) or {}).get("replied"):
                continue                      # пока ждали — человек ответил
            try:
                client = await get_client(slot)
                if client is None:
                    continue
                peer = await client.get_input_entity(int(uid))
                await asyncio.wait_for(client.delete_dialog(peer, revoke=True), 30)
            except FloodWaitError:
                break
            except ValueError:
                pass                          # Telegram уже не знает такого собеседника — просто освобождаем запись
            except Exception as e:
                log.warning("очистка диалога %s: %s: %s", k, type(e).__name__, e)
                continue
            if name:
                remove_processed(name)
            unset_dm_state(slot, uid)
            log_event("clean", slot, uid, name=name)
            cleaned += 1
        await asyncio.sleep(1)
    if cleaned:
        log.info("удалено диалогов без ответа: %s", cleaned)


async def cleanup_loop():
    await asyncio.sleep(60)
    while True:
        try:
            await cleanup_once()
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("очистка диалогов: ошибка цикла")
        await asyncio.sleep(NOREPLY_POLL)


# ---------------------------------------------------------
# Уведомление об окончании спам-блока
# ---------------------------------------------------------

async def spam_watch_loop():
    """Раз в минуту смотрит, не истёк ли срок спам-блока у аккаунтов; когда истёк — перепроверяет в @SpamBot и пишет вам."""
    await asyncio.sleep(45)
    while True:
        now = time.time()
        for slot in list(spam_state):
            s = spam_state.get(slot) or {}
            if s.get("status") != "limited" or s.get("permanent") or not s.get("until"):
                continue
            if s["until"] > now or s.get("expired_notified"):
                continue
            s["expired_notified"] = True                    # ставим сразу, чтобы не слать дубли
            save_json(SPAM_FILE, spam_state)
            try:
                info = await check_spambot(slot)
            except Exception:
                info = {"status": "unknown"}
            if info.get("status") == "limited":
                info["expired_notified"] = not (info.get("until") and info["until"] > now)
                save_json(SPAM_FILE, spam_state)
                text = f"Внимание: Срок спам-блока истёк, но SpamBot ещё ограничивает\n{title(slot)}: {spam_summary(slot, info)}"
            elif info.get("status") == "free":
                text = f"<b>Спам-блок закончился</b>\n{title(slot)} снова может писать людям"
            else:
                text = f"Срок спам-блока у {title(slot)} истёк. Проверьте: /spam {slot}"
            await notify_admins(text)
        await asyncio.sleep(60)


# ---------------------------------------------------------
# Меню настроек
# ---------------------------------------------------------

def settings_view():
    cfg = load_config()
    n_src, n_bs = len(cfg["chat_source_groups"]), len(cfg["chat_exclude_groups"])
    n_off = len(cfg["chat_modes"]) - n_src - n_bs
    ents = [e for a in cfg["accounts"].values() for e in (a.get("schedule") or [])]
    first = str((cfg.get("messages") or [""])[0])
    wait = cfg.get("noreply_hours") or 0
    text = (
        "<b>НАСТРОЙКИ</b>\n"
        f"{LINE}\n"
        f"<b>Чаты:</b> ИСТ {n_src} · БС {n_bs} · ОТКЛ {n_off}\n"
        f"<b>Расписаний:</b> {len(ents)} (вкл {sum(1 for e in ents if e.get('on', True))})\n\n"
        "<b>Тексты</b>\n"
        f"• Первое сообщение: {'задано' if first.strip() else 'Внимание: не задано'} (/text)\n"
        f"• Ссылка: {'задана' if link_text_of(cfg) else 'Внимание: не задана'} (/text2)\n"
        f"• Когда лимит набран: {'задан' if limit_text_of(cfg) else 'Внимание: не задан'} (/text6)\n"
        f"• Отказ: {len(cfg.get('texts_refusal') or [])} · вопрос: {len(cfg.get('texts_question') or [])} · "
        f"«откуда контакт»: {len(cfg.get('texts_source') or [])} (/text3 · /text4 · /text5)\n\n"
        "<b>Параметры</b>\n"
        f"• Лимит за запуск: <b>{cfg['max_messages']}</b> (/limit)\n"
        f"• Ссылок в день: <b>{day_limit(cfg) or 'без лимита'}</b> · выдано сегодня: <b>{day_used()}</b> (/daylimit)\n"
        f"• Сканировать сообщений: <b>{cfg['scan_messages_limit']}</b> (/scan)\n"
        f"• Давность активности: <b>{cfg['max_inactive_days']}</b> дн. (/active)\n"
        f"• Пауза между отправками: <b>{cfg['delay_between_messages']}</b> с (/delay)\n"
        f"• Удалять диалог без ответа через: <b>{(str(wait) + ' ч') if wait else 'не удалять'}</b> (/wait)")
    kb = [[btn("Чаты", "cm:g:v"), btn("Расписание", "sc:home")],
          [btn("Тексты", "st:texts"), btn("Статистика", "m:stats")],
          [btn("Назад", "home")]]
    return text, InlineKeyboardMarkup(inline_keyboard=kb)


async def settings_button(call, parts):
    await call.answer()
    if parts and parts[0] == "texts":
        rows = [[btn(TEXT_LISTS[k][1], f"tx:{k}:v")] for k in TEXT_LISTS]
        rows.append([btn("Назад", "st:home")])
        await edit(call.message, f"<b>ТЕКСТЫ</b>\n{LINE}\nВыберите, что настроить:", InlineKeyboardMarkup(inline_keyboard=rows))
        return
    text, kb = settings_view()
    await edit(call.message, text, kb)


@router.message(Command("settings"))
@admin
async def cmd_settings(message: Message):
    text, kb = settings_view()
    await notify(message, text, kb)


# ---------------------------------------------------------
# Расписания: бот сам запускает рассылку за вас (у каждого аккаунта — свои дни, время и чаты)
# ---------------------------------------------------------

DAY_NAMES = ["Пн", "Вт", "Ср", "Чт", "Пт", "Сб", "Вс"]
SCHED_WINDOW = 1800      # сек: если бот был занят/перезапущен, расписание ещё сработает в течение этого окна


def parse_hhmm(value):
    m = re.fullmatch(r"(\d{1,2}):(\d{2})", str(value or ""))
    if not m or int(m[1]) > 23 or int(m[2]) > 59:
        return None
    return int(m[1]), int(m[2])


def fmt_days(days):
    d = sorted(set(days or []))
    if len(d) == 7:
        return "каждый день"
    if d == [0, 1, 2, 3, 4]:
        return "Пн–Пт"
    if d == [5, 6]:
        return "Сб, Вс"
    return ", ".join(DAY_NAMES[i] for i in d) or "дни не выбраны"


def find_entry(cfg, slot, eid):
    for e in (cfg["accounts"].get(slot) or {}).get("schedule") or []:
        if e.get("id") == eid:
            return e
    return None


def mutate_entry(slot, eid, fn):
    cfg = load_config()
    e = find_entry(cfg, slot, eid)
    if e is None:
        return False
    fn(e)
    save_config(cfg)
    return True


def entry_chats_text(cfg, slot, e):
    src, _ = account_chats(cfg, slot)
    if e.get("chats") is None:
        return f"все ИСТ аккаунта ({len(src)})"
    return f"выбрано {len([r for r in e['chats'] if r in src])} из {len(src)}"


def sched_home_view():
    cfg = load_config()
    cur = cur_tab(cfg)
    multi = len(cfg["tabs"]) > 1
    all_ents = [e for a in cfg["accounts"].values() for e in (a.get("schedule") or [])]
    tcounts = Counter(tab_of_entry(cfg, e) for e in all_ents)
    lines = ["<b>Расписание</b>\n<i>Бот сам запускает рассылку в нужные дни и время (UTC+7) — вам ничего делать не нужно. "
             "У каждого аккаунта свои расписания и свои чаты.</i>\n"
             f"Вкладка: <b>{esc('все' if cur == '*' else tab_name(cfg, cur))}</b>\n"]
    kb = tab_bar(cfg, "h", "-", tcounts)
    for s in slots_sorted(cfg):
        ents = [e for e in cfg["accounts"][s].get("schedule") or [] if cur == "*" or tab_of_entry(cfg, e) == cur]
        on = sum(1 for e in ents if e.get("on", True))
        lines.append(f"<b>{title(s)}</b>{role_mark(cfg, s)} — " + (f"расписаний: {len(ents)} (вкл {on})" if ents else "нет расписаний"))
        kb.append([btn(f"{s} · {short(strip_tags(title(s)), 24)} · {len(ents)} ", f"sc:a:{s}")])
    if not slots_sorted(cfg):
        lines.append("<i>нет аккаунтов — /account 1</i>")
    kb.append([btn("Назад", "st:home")])
    return "\n".join(lines), InlineKeyboardMarkup(inline_keyboard=kb)


def sched_account_view(slot):
    cfg = load_config()
    acc = cfg["accounts"].get(slot)
    if acc is None:
        return None
    cur = cur_tab(cfg)
    multi = len(cfg["tabs"]) > 1
    src, bs = account_chats(cfg, slot)
    off = len(cfg["chat_modes"]) - len(src) - len(bs)
    own = len(acc.get("chat_modes") or {})
    all_ents = acc.get("schedule") or []
    ents = [e for e in all_ents if cur == "*" or tab_of_entry(cfg, e) == cur]
    tcounts = Counter(tab_of_entry(cfg, e) for e in all_ents)

    def tag_of(e):
        return f" · [{esc(tab_name(cfg, tab_of_entry(cfg, e)))}]" if multi and cur == "*" else ""

    rows = [f"{n}. {fmt_days(e.get('days'))} · {e.get('time', '--:--')} · {entry_chats_text(cfg, slot, e)} · "
            f"{'вкл' if e.get('on', True) else 'выкл'}{tag_of(e)}" for n, e in enumerate(ents, 1)]
    text = (f"<b>{title(slot)}</b>{role_mark(cfg, slot)}\n"
            f"Вкладка: <b>{esc('все' if cur == '*' else tab_name(cfg, cur))}</b>\n"
            f"Чаты: ИСТ {len(src)} · БС {len(bs)} · ОТКЛ {off}" + (f" · личных поправок: {own}" if own else "") + "\n\n"
            + ("\n".join(rows) if rows else "<i>в этой вкладке расписаний пока нет</i>")
            + "\n\n<i>Время — UTC+7. Запуск идёт от этого аккаунта как отправителя.</i>")
    kb = tab_bar(cfg, "s", slot, tcounts)
    kb += [[btn(f"{n}. {fmt_days(e.get('days'))} {e.get('time', '--:--')} {'вкл' if e.get('on', True) else 'выкл'}", f"sc:e:{slot}:{e['id']}")]
           for n, e in enumerate(ents, 1)]
    kb.append([btn("Добавить расписание", f"sc:add:{slot}")])
    kb.append([btn("Чаты этого аккаунта", f"cm:{slot}:v")])
    kb.append([btn("Назад", "sc:home")])
    return text, InlineKeyboardMarkup(inline_keyboard=kb)


def sched_entry_view(slot, eid):
    cfg = load_config()
    e = find_entry(cfg, slot, eid)
    if e is None:
        return None
    days = set(e.get("days") or [])
    on = e.get("on", True)
    tname = tab_name(cfg, tab_of_entry(cfg, e))
    text = (f"<b>Расписание · {title(slot)}</b>\n\n"
            f"Вкладка: <b>{esc(tname)}</b>\n"
            f"Дни: <b>{fmt_days(days)}</b>\nВремя: <b>{esc(e.get('time', '12:00'))}</b> (UTC+7)\n"
            f"Чаты: {entry_chats_text(cfg, slot, e)}\n"
            f"Статус: {'включено' if on else 'выключено — нажмите «Включить»'}\n\n"
            "<i>В это время бот сам запустит рассылку: возьмёт людей из выбранных чатов ИСТ, проверит БС и напишет.</i>")
    base = f"{slot}:{eid}"
    kb = [[btn(("" if i in days else "") + DAY_NAMES[i], f"sc:d:{base}:{i}") for i in range(7)],
          [btn("Будни", f"sc:d:{base}:w"), btn("Каждый день", f"sc:d:{base}:a")],
          [btn(f"Время {e.get('time', '12:00')}", f"sc:t:{base}"), btn("Чаты", f"sc:c:{base}")]]
    if len(cfg["tabs"]) > 1:
        kb.append([btn(f"Вкладка: {short(tname, 18)} →", f"sc:tb:{base}")])
    kb += [[btn("Выключить" if on else "Включить", f"sc:on:{base}"), btn("Удалить", f"sc:del:{base}")],
           [btn("Запустить сейчас", f"sc:run:{base}"), btn("Назад", f"sc:a:{slot}")]]
    return text, InlineKeyboardMarkup(inline_keyboard=kb)


def sched_hours_view(slot, eid):
    base = f"{slot}:{eid}"
    hours = [btn(f"{h:02d}", f"sc:h:{base}:{h:02d}") for h in range(24)]
    kb = [hours[i:i + 6] for i in range(0, 24, 6)]
    kb.append([btn("Назад", f"sc:e:{base}")])
    return "<b>Во сколько запускать?</b>\nВыберите час (UTC+7):", InlineKeyboardMarkup(inline_keyboard=kb)


def sched_minutes_view(slot, eid, hour):
    base = f"{slot}:{eid}"
    mins = [btn(f"{hour}:{m:02d}", f"sc:m:{base}:{hour}:{m:02d}") for m in range(0, 60, 5)]
    kb = [mins[i:i + 4] for i in range(0, 12, 4)]
    kb.append([btn("Часы", f"sc:t:{base}")])
    return f"<b>Минуты</b>\nЧас: {hour}. Выберите время (UTC+7):", InlineKeyboardMarkup(inline_keyboard=kb)


def sched_chats_view(slot, eid):
    cfg = load_config()
    e = find_entry(cfg, slot, eid)
    if e is None:
        return None
    src, _ = account_chats(cfg, slot)
    chosen = set(src) if e.get("chats") is None else set(e["chats"])
    base = f"{slot}:{eid}"
    kb = []
    for ref in src:
        name = chat_name_cache.get(ref) or ref
        kb.append([btn(("" if ref in chosen else "") + short(name, 36), f"sc:k:{base}:{chash(ref)}")])
    kb.append([btn("Все ИСТ (по умолчанию)", f"sc:ka:{base}")])
    kb.append([btn("Назад", f"sc:e:{base}")])
    text = (f"<b>Чаты для расписания · {title(slot)}</b>\n"
            "<i>Отмечены чаты, которые берём в это время. Список — только чаты в режиме ИСТ у этого аккаунта.</i>\n\n"
            + (f"Выбрано: {len([r for r in src if r in chosen])} из {len(src)}" if src else
               "Внимание: У аккаунта нет чатов в режиме ИСТ — включите их в «Чаты этого аккаунта»."))
    return text, InlineKeyboardMarkup(inline_keyboard=kb)


async def sched_button(call, parts):
    act, a = (parts[0] if parts else "home"), parts[1:]
    cfg = load_config()

    async def show(view, toast=None):
        if view is None:
            await call.answer("Это уже удалено", show_alert=True)
            return
        await call.answer(toast)
        await show_pages(call, *view)

    if act == "home":
        await show(sched_home_view())
        return
    slot = a[0] if a else ""
    if slot not in cfg["accounts"]:
        await call.answer("Такого аккаунта уже нет", show_alert=True)
        return
    eid = a[1] if len(a) > 1 else ""
    if act == "a":
        await show(sched_account_view(slot))
    elif act == "add":
        eid = f"{random.getrandbits(24):06x}"
        _cur = cur_tab(cfg)
        cfg["accounts"][slot].setdefault("schedule", []).append(
            {"id": eid, "days": [0, 1, 2, 3, 4], "time": "12:00", "chats": None, "on": False,
             "tab": _cur if _cur != "*" else cfg["tabs"][0]["id"]})
        save_config(cfg)
        await show(sched_entry_view(slot, eid), "Создано (выключено) — настройте и включите")
    elif act == "e":
        await show(sched_entry_view(slot, eid))
    elif act == "d" and len(a) > 2:
        def toggle(e):
            days = set(e.get("days") or [])
            if a[2] == "w":
                days = {0, 1, 2, 3, 4}
            elif a[2] == "a":
                days = set(range(7))
            elif a[2].isdigit() and int(a[2]) < 7:
                days ^= {int(a[2])}
            e["days"] = sorted(days)
        mutate_entry(slot, eid, toggle)
        await show(sched_entry_view(slot, eid))
    elif act == "t":
        await show(sched_hours_view(slot, eid))
    elif act == "h" and len(a) > 2:
        await show(sched_minutes_view(slot, eid, a[2]))
    elif act == "m" and len(a) > 3 and parse_hhmm(f"{a[2]}:{a[3]}"):
        mutate_entry(slot, eid, lambda e: e.update(time=f"{int(a[2]):02d}:{a[3]}"))
        await show(sched_entry_view(slot, eid), "Время сохранено")
    elif act == "tb":                          # перенести расписание в следующую вкладку
        mutate_entry(slot, eid, lambda e: e.update(tab=next_tab(cfg, tab_of_entry(cfg, e))))
        await show(sched_entry_view(slot, eid), "Перенесено")
    elif act == "on":
        mutate_entry(slot, eid, lambda e: e.update(on=not e.get("on", True)))
        await show(sched_entry_view(slot, eid))
    elif act == "del":
        def drop(c):
            c["accounts"][slot]["schedule"] = [e for e in c["accounts"][slot].get("schedule") or [] if e.get("id") != eid]
        drop(cfg)
        save_config(cfg)
        await show(sched_account_view(slot), "Удалено")
    elif act == "run":
        e = find_entry(cfg, slot, eid)
        if e is None:
            await call.answer("Это уже удалено", show_alert=True)
            return
        if run_locks:
            await call.answer("Рассылка уже идёт — /stop, чтобы остановить", show_alert=True)
            return
        await call.answer("Запускаю…")
        spawn(run_scheduled(slot, dict(e), manual=True))
    elif act == "c":
        await show(sched_chats_view(slot, eid))
    elif act in ("k", "ka"):
        def pick(e):
            src, _ = account_chats(load_config(), slot)
            if act == "ka":
                e["chats"] = None
                return
            ref = ref_by_hash(src, a[2]) if len(a) > 2 else None
            if ref is None:
                return
            chosen = set(src) if e.get("chats") is None else set(e["chats"])
            chosen ^= {ref}
            e["chats"] = None if chosen >= set(src) else [r for r in src if r in chosen]
        mutate_entry(slot, eid, pick)
        await show(sched_chats_view(slot, eid))
    else:
        await call.answer()


@router.message(Command("schedule", "plan"))
@admin
async def cmd_schedule(message: Message):
    text, kb = sched_home_view()
    await notify(message, text, kb)


class AdminTarget:
    """Подставляется вместо Message: сообщения запуска по расписанию уходят всем админам бота."""

    class _Sent:
        def __init__(self, msgs):
            self.msgs = msgs

        async def delete(self):
            for m in self.msgs:
                with suppress(Exception):
                    await m.delete()

    async def answer(self, text, parse_mode=None, reply_markup=None, **kw):
        bot = bot_ref["bot"]
        sent, err = [], None
        for aid in sorted(admin_ids):
            try:
                sent.append(await bot.send_message(aid, text, parse_mode=parse_mode, reply_markup=reply_markup))
            except Exception as e:
                err = e
        if not sent and err is not None:
            raise err
        return AdminTarget._Sent(sent)


async def run_scheduled(slot, e, manual=False):
    target = AdminTarget()
    cfg = load_config()
    if slot not in cfg["accounts"]:
        return
    waited = 0
    while run_locks and waited < 3600:          # идёт другая рассылка (ручная или другого аккаунта) — ждём очереди
        await asyncio.sleep(15)
        waited += 15
    if run_locks:
        await notify(target, f"Расписание {title(slot)} {esc(e.get('time', ''))} пропущено: другая рассылка шла больше часа")
        return
    rc = run_cfg(cfg, snd=slot, col=pick_collector(cfg, slot), chats=e.get("chats"))
    head = "<b>Запуск по кнопке</b>" if manual else "<b>Запуск по расписанию</b>"
    await notify(target, f"{head} · {title(slot)} · {fmt_days(e.get('days'))} {esc(e.get('time', ''))}")
    await asyncio.create_task(run_collection_and_send(target, rc, 0))


async def schedule_tick():
    cfg = load_config()
    now = datetime.now(SPAM_TZ)
    state = load_json(SCHED_FILE, {})
    due = []
    for slot in slots_sorted(cfg):
        for e in cfg["accounts"][slot].get("schedule") or []:
            hm = parse_hhmm(e.get("time"))
            if not e.get("on", True) or hm is None or not e.get("id") or now.weekday() not in (e.get("days") or []):
                continue
            planned = now.replace(hour=hm[0], minute=hm[1], second=0, microsecond=0)
            stamp = planned.strftime("%Y-%m-%d %H:%M")
            if 0 <= (now - planned).total_seconds() <= SCHED_WINDOW and state.get(e["id"]) != stamp:
                due.append((slot, dict(e), stamp))
    for slot, e, stamp in due:
        state[e["id"]] = stamp              # помечаем ДО запуска: не сработает дважды
        save_json(SCHED_FILE, state)
        await run_scheduled(slot, e)


async def schedule_loop():
    await asyncio.sleep(30)
    while True:
        try:
            await schedule_tick()
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("расписание: ошибка цикла")
        await asyncio.sleep(20)


# ---------------------------------------------------------
# Запуск
dp.include_router(router)

BOT_COMMANDS = [
    ("start", "Аккаунты и статус"), ("command", "Список команд"), ("run", "Запустить рассылку"),
    ("stop", "Остановить"), ("daylimit", "Лимит ссылок в день"), ("chats", "Чаты: ИСТ / БС / ОТКЛ"), ("schedule", "Расписание"), ("settings", "Настройки"), ("login", "Войти в аккаунт"),
    ("info", "Информация о человеке"), ("stats", "Статистика за день"), ("text", "Тексты"), ("spam", "Проверить спам-блок"), ("cancel", "Отмена"),
]


async def supervise(name, factory):
    """Фоновая задача, которая сама перезапускается, если упала."""
    while True:
        try:
            await factory()
            return
        except asyncio.CancelledError:
            raise
        except Exception:
            log.exception("%s: сбой, перезапуск через 5 с", name)
            await asyncio.sleep(5)


async def main():
    setup_logging()
    cfg = load_config()
    token = cfg.get("bot_token") or os.environ.get("BOT_TOKEN")
    if not token:
        raise ValueError("Укажите bot_token в config.json или переменную окружения BOT_TOKEN")
    # защита от двух одновременно запущенных копий (из-за них бывают дубли сообщений и «через раз» команды)
    lock = socket.socket()
    try:
        lock.bind(("127.0.0.1", int(cfg.get("instance_port", 47213))))
    except OSError:
        print("Ошибка: Бот уже запущен в другом окне/процессе. Закройте его и запустите заново.")
        return
    bot = Bot(token=token)
    bot_ref["bot"] = bot
    load_state()
    with suppress(Exception):
        await bot.set_my_commands([BotCommand(command=c, description=d) for c, d in BOT_COMMANDS])
    # аккаунты подключаются в фоне и параллельно: бот отвечает на команды сразу, а не после подключения всех аккаунтов
    tasks = [
        asyncio.create_task(connect_all()),
        asyncio.create_task(supervise("таймер спам-блока", spam_watch_loop)),
        asyncio.create_task(supervise("сторож соединений", watchdog_loop)),
        asyncio.create_task(supervise("очистка диалогов без ответа", cleanup_loop)),
        asyncio.create_task(supervise("расписание", schedule_loop)),
    ]
    print("Бот запущен. Аккаунты подключаются в фоне…")
    try:
        await dp.start_polling(bot)
    finally:
        for t in tasks:
            t.cancel()
        await asyncio.gather(*tasks, return_exceptions=True)
        for uid in list(login):
            await close_login(uid)
        await drop_all()
        flush_saves()
        await bot.session.close()


if __name__ == "__main__":
    asyncio.run(main())

