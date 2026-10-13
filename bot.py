"""
Кейсорока 🐦 — Telegram-бот с идеями для бизнеса.

Собирает материалы из открытых RSS-лент, показывает дайджест,
хранит интересы и избранное каждого пользователя в SQLite.
"""

from __future__ import annotations

import asyncio
import html
import logging
import os
import random
import re
import sqlite3
import sys
from contextlib import closing
from datetime import datetime, time as dt_time, timezone
from html.parser import HTMLParser
from urllib.parse import parse_qsl, urlencode, urlsplit, urlunsplit
from typing import Any
from zoneinfo import ZoneInfo

import feedparser
import requests
from dotenv import load_dotenv
from telegram import (
    InlineKeyboardButton,
    InlineKeyboardMarkup,
    ReplyKeyboardMarkup,
    Update,
)
from telegram.constants import ParseMode
from telegram.error import TelegramError
from telegram.ext import (
    Application,
    CallbackQueryHandler,
    CommandHandler,
    ContextTypes,
    MessageHandler,
    filters,
)

# ---------------------------------------------------------------------------
# Конфигурация
# ---------------------------------------------------------------------------

# Все RSS-источники в одном месте. Русские ленты идут первыми — это приоритет дайджеста.
# lang: ru — русскоязычное издание, en — зарубежное (используем как запасной фонд).
RSS_SOURCES: list[dict[str, str]] = [
    {"name": "Inc. Россия", "url": "https://incrussia.ru/feed/", "lang": "ru"},
    {"name": "VC.ru", "url": "https://vc.ru/rss", "lang": "ru"},
    {
        "name": "Rusbase",
        "url": "https://rb.ru/feeds/tag/startupoftheday/",
        "lang": "ru",
    },
    {"name": "Cossa", "url": "https://www.cossa.ru/rss/", "lang": "ru"},
    {"name": "Retail.ru", "url": "https://www.retail.ru/rss/news/", "lang": "ru"},
    {
        "name": "Entrepreneur",
        "url": "https://www.entrepreneur.com/latest.rss",
        "lang": "en",
    },
    {"name": "Inc.", "url": "https://www.inc.com/rss/homepage.xml", "lang": "en"},
]

# Файл базы рядом со скриптом, чтобы данные не терялись при перезапуске.
BASE_DIR = os.path.dirname(os.path.abspath(__file__))
DB_PATH = os.getenv("DB_PATH", os.path.join(BASE_DIR, "keysoroka.db"))

REQUEST_TIMEOUT = 15  # секунд на загрузку одной RSS-ленты
USER_AGENT = "KeysorokaBot/1.0 (educational Telegram bot)"
MAX_FEED_ITEMS = 30  # с одной ленты берём не всё подряд
DIGEST_MIN = 3
DIGEST_MAX = 5
SUMMARY_LIMIT = 420
DETAIL_LIMIT = 230
MIN_DIGEST_SCORE = 5  # ниже — статья слишком слабо связана с бизнесом
MIN_RANDOM_SCORE = 7

# Состояние ожидания ключевых слов (проще, чем ConversationHandler).
AWAITING_INTERESTS = "awaiting_interests"

# Тексты кнопок главного меню.
BTN_DIGEST = "📰 Свежие находки"
BTN_RANDOM = "💡 Случайная идея"
BTN_SAVED = "⭐ Моё гнездо"
BTN_INTERESTS = "🔎 Мои интересы"
BTN_DIGEST_SETTINGS = "🔔 Настройка рассылки"


# Готовые отрасли из предложения тестировщика лабораторной №3.
# Используем уже существующий фильтр интересов: менять структуру SQLite не нужно.
# Выбор отрасли заменяет текущий список ключевых слов пользователя.
INDUSTRIES: dict[str, tuple[str, str]] = {
    "tech": (
        "💻 IT и технологии",
        "технологии, искусственный интеллект, нейросети, software, saas",
    ),
    "retail": (
        "🛍 Торговля и ритейл",
        "ритейл, торговля, магазин, маркетплейс, retail",
    ),
    "marketing": (
        "📣 Маркетинг и реклама",
        "маркетинг, реклама, продвижение, бренд, advertising",
    ),
    "finance": (
        "💰 Финансы",
        "финансы, инвестиции, финтех, банки, fintech",
    ),
    "food": (
        "🍽 Рестораны и еда",
        "ресторан, кафе, общепит, доставка еды, foodtech",
    ),
}

INTRO_PHRASES = [
    "Кар-р! Есть свежая находка!",
    "Принесла на хвосте кое-что интересное.",
    "А вот это уже пахнет бизнес-идеей!",
    "Забирай в гнездо, пригодится!",
    "Интересно придумали, правда?",
    "Глянь, какая штучка попалась в полёте.",
    "Сегодня лента особенно любопытная.",
    "Тут пахнет не новостью, а возможностью.",
    "Осторожно: может вызвать желание открыть своё дело.",
]

DIGEST_INTROS = [
    "Кар-р! Слетала по русским деловым лентам и принесла несколько находок.",
    "Собрала коротко и по делу — без гигантских карточек сайтов.",
    "Ну что, посмотрим, кто сегодня придумал что-нибудь гениальное? 👀",
]

EMPTY_DIGEST_PHRASES = [
    "По твоим интересам сейчас пусто. Измени ключевые слова или очисти фильтр — тогда принесу шире.",
    "Ничего подходящего не нашла. Попробуй другое слово или сними фильтр в «Моих интересах».",
]

# Русские и английские аналоги для фильтра интересов.
KEYWORD_ALIASES: list[set[str]] = [
    {"маркетинг", "маркетинга", "маркетинговый", "маркетинговые", "marketing"},
    {"стартап", "стартапы", "стартапа", "стартапов", "startup", "startups", "start-up"},
    {"бизнес", "бизнеса", "бизнесу", "business"},
    {
        "предприниматель",
        "предпринимателя",
        "предприниматели",
        "предпринимательство",
        "entrepreneur",
        "entrepreneurs",
        "founder",
        "founders",
    },
    {"подписка", "подписки", "подписке", "subscription", "subscriptions", "saas"},
    {"франшиза", "франшизы", "франшизу", "franchise", "franchising"},
    {"продажи", "продаж", "продажа", "продажам", "sales", "selling"},
    {
        "инвестиции",
        "инвестиций",
        "инвестиция",
        "investment",
        "investments",
        "funding",
        "venture",
    },
    {"ритейл", "ритейла", "розница", "розничной", "retail"},
    {"реклама", "рекламы", "рекламный", "рекламе", "advertising", "ads"},
    {"монетизация", "монетизации", "monetization", "monetisation"},
    {"кейс", "кейсы", "кейса", "case", "cases"},
    {"ниша", "ниши", "нишу", "niche"},
]

# Маркеры бизнес-тематики для простой оценки релевантности.
IDEA_MARKERS = (
    "бизнес-модел",
    "бизнес модел",
    "монетизац",
    "подписк",
    "франшиз",
    "ниш",
    "saas",
    "маркетплейс",
    "юнит-эконом",
    "тариф",
    "комисси",
    "subscription",
    "franchise",
    "business model",
    "monetiz",
    "marketplace",
)
CASE_MARKERS = (
    "кейс",
    "маркетинг",
    "реклам",
    "продаж",
    "бренд",
    "лояльност",
    "клиент",
    "конверси",
    "воронк",
    "кампани",
    "rebrand",
    "case study",
    "marketing",
    "advertising",
    "campaign",
    "retention",
    "conversion",
)
STARTUP_MARKERS = (
    "стартап",
    "startup",
    "основател",
    "founder",
    "предпринима",
    "раунд",
    "венчур",
    "акселератор",
    "пивот",
    "mvp",
    "seed",
    "funding",
    "venture",
)
GENERAL_BIZ_MARKERS = (
    "бизнес",
    "компан",
    "выручк",
    "прибыл",
    "рынк",
    "ритейл",
    "услуг",
    "продукт",
    "инвестиц",
    "business",
    "company",
    "entrepreneur",
    "revenue",
    "retail",
    "sales",
    "startup",
)
NEGATIVE_MARKERS = (
    "санкц",
    "безвизов",
    "выборы",
    "госдум",
    "футбол",
    "хоккей",
    "чемпионат",
    "рецепт",
    "погод",
    "сериал",
    "кинопремьер",
    "концерт",
    "клип",
    "iphone",
    "ipad mini",
    "чипсет",
    "видеокарт",
)

RSS_NOISE_PATTERNS = (
    r"The post .+ appeared first on .+",
    r"Читать далее.*$",
    r"Read more.*$",
    r"Continue reading.*$",
    r"Поделиться.*$",
    r"Подписывайтесь на .*",
    r"Subscribe to .*",
    r"The post appeared first.*",
)

WELCOME_TEXT = (
    "Кар-р! 🐦 Привет! Я Кейсорока.\n\n"
    "Летаю по интернету и собираю самые любопытные бизнес-идеи, "
    "необычные стартапы и хитрые решения компаний.\n\n"
    "Обещаю: никакой скучной воды. Только интересные находки!\n\n"
    "Ну что, посмотрим, кто сегодня придумал что-нибудь гениальное? 👀"
)

MAIN_KEYBOARD = ReplyKeyboardMarkup(
    [
        [BTN_DIGEST, BTN_RANDOM],
        [BTN_SAVED, BTN_INTERESTS],
        [BTN_DIGEST_SETTINGS],
    ],
    resize_keyboard=True,
)

logger = logging.getLogger("keysoroka")


# ---------------------------------------------------------------------------
# Вспомогательные функции для текста
# ---------------------------------------------------------------------------


class _HTMLStripper(HTMLParser):
    """Простой съёмщик HTML-тегов из описаний RSS."""

    def __init__(self) -> None:
        super().__init__()
        self.parts: list[str] = []

    def handle_data(self, data: str) -> None:
        self.parts.append(data)

    def get_text(self) -> str:
        return " ".join(self.parts)


def strip_html(raw: str | None) -> str:
    """Убирает HTML и лишние пробелы из текста RSS."""
    if not raw:
        return ""
    parser = _HTMLStripper()
    try:
        parser.feed(raw)
        text = parser.get_text()
    except Exception:
        text = re.sub(r"<[^>]+>", " ", raw)
    text = html.unescape(text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def clean_rss_text(raw: str | None) -> str:
    """Снимает HTML и типичный рекламный хвост RSS."""
    text = strip_html(raw)
    for pattern in RSS_NOISE_PATTERNS:
        text = re.sub(pattern, " ", text, flags=re.IGNORECASE)
    text = re.sub(r"https?://\S+", " ", text)
    text = re.sub(r"\s+", " ", text).strip()
    return text


def has_meaningful_description(value: str | None) -> bool:
    """Отбрасывает пустые RSS-анонсы, заглушки и бессодержательный текст.

    Проверка не обращается к внешним сервисам и применяется как к новым
    публикациям, так и к статьям, уже сохранённым в SQLite.
    """
    text = re.sub(r"\s+", " ", value or "").strip()
    normalized = text.strip(" \t\r\n.,:;!?…—–-_()[]{}<>\"'").casefold()
    if normalized in {"xxx", "ххх", "n/a", "na", "none", "null", "undefined", "tbd", "lorem ipsum", "нет описания", "описание отсутствует", "no description"}:
        return False
    if re.fullmatch(r"[xх]{2,}", normalized):
        return False
    # Одно-два слова обычно не объясняют суть материала.
    if len(normalized) < 25:
        return False
    return len(re.findall(r"[A-Za-zА-Яа-яЁё]", normalized)) >= 12


def shorten(text: str, limit: int) -> str:
    """Сокращает текст, не обрывая слово слишком грубо."""
    if len(text) <= limit:
        return text
    cut = text[: limit + 1]
    if " " in cut:
        cut = cut.rsplit(" ", 1)[0]
    return cut.rstrip(".,;: ") + "…"


def split_sentences(text: str) -> list[str]:
    parts = re.split(r"(?<=[.!?])\s+", text)
    return [p.strip() for p in parts if p.strip()]


def is_complete_sentence(text: str) -> bool:
    """Предложение кончается знаком пунктуации, а не многоточием RSS-анонса."""
    text = text.strip().rstrip('»"”)]')
    return text.endswith((".", "!", "?")) and not text.endswith(("...", "..", "…"))


def complete_excerpt(text: str, limit: int = SUMMARY_LIMIT, max_sentences: int = 2) -> str:
    """Не обрывает предложения на «которые…» или посередине мысли.

    Если RSS прислал незавершённый фрагмент, оставляем только предыдущие
    законченные предложения. Если нет ни одного — откажемся от фрагмента.
    """
    if not has_meaningful_description(text):
        return ""
    selected: list[str] = []
    for sentence in split_sentences(text):
        if not is_complete_sentence(sentence):
            break
        candidate = " ".join([*selected, sentence])
        if len(candidate) > limit:
            break
        selected.append(sentence)
        if len(selected) >= max_sentences:
            break
    # У некоторых RSS описания без точки; показываем только короткие и целые.
    if not selected and len(text) <= limit and not text.rstrip().endswith(("…", "...")):
        return text.strip()
    return " ".join(selected)


def redundant_detail(summary: str, detail: str) -> bool:
    """Проверяем повтор, в том числе частично обрезанного предложения."""
    if not detail.strip():
        return True
    def normalize(value: str) -> str:
        return re.sub(r"\s+", " ", re.sub(r"[^\w\s]", " ", value.casefold())).strip()
    base, candidate = normalize(summary), normalize(detail)
    if not candidate:
        return True
    # Если начало детали встречается в старом описании, это повтор той же мысли.
    if candidate[:45] and candidate[:45] in base:
        return True
    a, b = set(base.split()), set(candidate.split())
    return bool(b and len(b) >= 6 and len(a & b) / len(b) > 0.76)


def pick_summary_and_detail(description: str, title: str = "") -> tuple[str, str]:
    """Аккуратная суть и только отдельная, неповторяющаяся деталь из источника."""
    if not has_meaningful_description(description):
        return "", ""
    sentences = split_sentences(description)
    summary = complete_excerpt(description)
    if not summary:
        return "", ""
    used = len(split_sentences(summary))
    detail = ""
    for candidate in sentences[used:]:
        if not is_complete_sentence(candidate):
            continue
        if len(candidate) > DETAIL_LIMIT:
            continue
        if _is_useful_detail(candidate, title, summary) and not redundant_detail(summary, candidate):
            detail = candidate
            break
    return summary, detail


def _is_useful_detail(candidate: str, title: str, summary: str) -> bool:
    """Деталь должна быть из текста источника и нести хоть какой-то смысл."""
    text = candidate.strip()
    if len(text) < 40:
        return False
    low = text.lower()
    title_low = (title or "").lower()
    if title_low and (low.startswith(title_low[:40]) or title_low.startswith(low[:40])):
        return False
    if text in summary:
        return False
    if any(noise in low for noise in ("подписывайтесь", "subscribe", "читайте также", "read more")):
        return False
    has_number = bool(re.search(r"\d", text))
    has_biz = any(mark in low for mark in IDEA_MARKERS + CASE_MARKERS + STARTUP_MARKERS + GENERAL_BIZ_MARKERS)
    return has_number or has_biz


def html_escape(text: str) -> str:
    return html.escape(text, quote=False)


_last_intro: str | None = None


def next_intro() -> str:
    """Не повторяет одну и ту же фразу подряд."""
    global _last_intro
    choices = [p for p in INTRO_PHRASES if p != _last_intro] or list(INTRO_PHRASES)
    phrase = random.choice(choices)
    _last_intro = phrase
    return phrase


def random_intro() -> str:
    return next_intro()


def is_russian_text(text: str) -> bool:
    return bool(re.search(r"[А-Яа-яЁё]", text or ""))


def parse_digest_time(value: str) -> dt_time:
    """Разбирает DIGEST_TIME вида 09:00."""
    try:
        hour_str, minute_str = value.strip().split(":")
        hour, minute = int(hour_str), int(minute_str)
        if not (0 <= hour <= 23 and 0 <= minute <= 59):
            raise ValueError
        return dt_time(hour=hour, minute=minute)
    except Exception:
        logger.warning("Некорректный DIGEST_TIME=%s, использую 09:00", value)
        return dt_time(hour=9, minute=0)


# ---------------------------------------------------------------------------
# База данных
# ---------------------------------------------------------------------------


def get_connection() -> sqlite3.Connection:
    conn = sqlite3.connect(DB_PATH)
    conn.row_factory = sqlite3.Row
    conn.execute("PRAGMA foreign_keys = ON")
    return conn


def init_db() -> None:
    """Создаёт таблицы при первом запуске."""
    with closing(get_connection()) as conn:
        conn.executescript(
            """
            CREATE TABLE IF NOT EXISTS users (
                telegram_id INTEGER PRIMARY KEY,
                digest_enabled INTEGER NOT NULL DEFAULT 1,
                interests TEXT NOT NULL DEFAULT '',
                created_at TEXT NOT NULL
            );

            CREATE TABLE IF NOT EXISTS articles (
                id INTEGER PRIMARY KEY AUTOINCREMENT,
                guid TEXT NOT NULL UNIQUE,
                title TEXT NOT NULL,
                summary TEXT NOT NULL DEFAULT '',
                detail TEXT NOT NULL DEFAULT '',
                url TEXT NOT NULL,
                source TEXT NOT NULL,
                published_at TEXT
            );

            CREATE TABLE IF NOT EXISTS favorites (
                user_id INTEGER NOT NULL,
                article_id INTEGER NOT NULL,
                saved_at TEXT NOT NULL,
                PRIMARY KEY (user_id, article_id),
                FOREIGN KEY (user_id) REFERENCES users(telegram_id),
                FOREIGN KEY (article_id) REFERENCES articles(id)
            );

            -- История отправок отдельная для каждого пользователя.
            -- Старые избранные материалы и интересы не меняем.
            CREATE TABLE IF NOT EXISTS delivered_articles (
                user_id INTEGER NOT NULL,
                article_id INTEGER NOT NULL,
                delivered_at TEXT NOT NULL,
                PRIMARY KEY (user_id, article_id),
                FOREIGN KEY (user_id) REFERENCES users(telegram_id),
                FOREIGN KEY (article_id) REFERENCES articles(id)
            );
            """
        )
        conn.commit()


def ensure_user(telegram_id: int) -> None:
    now = datetime.now(timezone.utc).isoformat()
    with closing(get_connection()) as conn:
        conn.execute(
            """
            INSERT OR IGNORE INTO users (telegram_id, digest_enabled, interests, created_at)
            VALUES (?, 1, '', ?)
            """,
            (telegram_id, now),
        )
        conn.commit()


def get_user(telegram_id: int) -> sqlite3.Row | None:
    with closing(get_connection()) as conn:
        return conn.execute(
            "SELECT * FROM users WHERE telegram_id = ?",
            (telegram_id,),
        ).fetchone()


def set_interests(telegram_id: int, interests: str) -> None:
    ensure_user(telegram_id)
    with closing(get_connection()) as conn:
        conn.execute(
            "UPDATE users SET interests = ? WHERE telegram_id = ?",
            (interests, telegram_id),
        )
        conn.commit()


def set_digest_enabled(telegram_id: int, enabled: bool) -> None:
    ensure_user(telegram_id)
    with closing(get_connection()) as conn:
        conn.execute(
            "UPDATE users SET digest_enabled = ? WHERE telegram_id = ?",
            (1 if enabled else 0, telegram_id),
        )
        conn.commit()


def list_digest_users() -> list[sqlite3.Row]:
    with closing(get_connection()) as conn:
        return conn.execute(
            "SELECT * FROM users WHERE digest_enabled = 1"
        ).fetchall()


def save_article(article: dict[str, Any]) -> int:
    """Сохраняет статью и возвращает её id. Дубликаты по guid не создаются."""
    with closing(get_connection()) as conn:
        conn.execute(
            """
            INSERT INTO articles (guid, title, summary, detail, url, source, published_at)
            VALUES (?, ?, ?, ?, ?, ?, ?)
            ON CONFLICT(guid) DO UPDATE SET
                title = excluded.title,
                summary = excluded.summary,
                detail = excluded.detail,
                url = excluded.url,
                source = excluded.source,
                published_at = excluded.published_at
            """,
            (
                article["guid"],
                article["title"],
                article["summary"],
                article["detail"],
                article["url"],
                article["source"],
                article.get("published_at"),
            ),
        )
        row = conn.execute(
            "SELECT id FROM articles WHERE guid = ?",
            (article["guid"],),
        ).fetchone()
        conn.commit()
        return int(row["id"])


def get_article(article_id: int) -> sqlite3.Row | None:
    with closing(get_connection()) as conn:
        return conn.execute(
            "SELECT * FROM articles WHERE id = ?",
            (article_id,),
        ).fetchone()


def articles_count() -> int:
    with closing(get_connection()) as conn:
        row = conn.execute("SELECT COUNT(*) AS n FROM articles").fetchone()
        return int(row["n"])


def add_favorite(user_id: int, article_id: int) -> bool:
    """Возвращает True, если запись новая."""
    ensure_user(user_id)
    now = datetime.now(timezone.utc).isoformat()
    with closing(get_connection()) as conn:
        cursor = conn.execute(
            """
            INSERT OR IGNORE INTO favorites (user_id, article_id, saved_at)
            VALUES (?, ?, ?)
            """,
            (user_id, article_id, now),
        )
        conn.commit()
        return cursor.rowcount > 0


def remove_favorite(user_id: int, article_id: int) -> None:
    with closing(get_connection()) as conn:
        conn.execute(
            "DELETE FROM favorites WHERE user_id = ? AND article_id = ?",
            (user_id, article_id),
        )
        conn.commit()


def list_favorites(user_id: int) -> list[sqlite3.Row]:
    with closing(get_connection()) as conn:
        return conn.execute(
            """
            SELECT a.*
            FROM favorites f
            JOIN articles a ON a.id = f.article_id
            WHERE f.user_id = ?
            ORDER BY f.saved_at DESC
            """,
            (user_id,),
        ).fetchall()


def delivered_article_ids(user_id: int) -> set[int]:
    """Исключает уже показанные статьи даже при смене ссылки или GUID в RSS."""
    with closing(get_connection()) as conn:
        delivered = conn.execute(
            """SELECT a.id, a.url, a.title FROM delivered_articles d
               JOIN articles a ON a.id = d.article_id WHERE d.user_id = ?""",
            (user_id,),
        ).fetchall()
        if not delivered:
            return set()
        seen_urls = {canonical_url(str(row["url"])) for row in delivered}
        seen_titles = {normalized_title(str(row["title"])) for row in delivered}
        result = {int(row["id"]) for row in delivered}
        for article in conn.execute("SELECT id, url, title FROM articles"):
            if (canonical_url(str(article["url"])) in seen_urls
                    or normalized_title(str(article["title"])) in seen_titles):
                result.add(int(article["id"]))
        return result


def mark_delivered(user_id: int, article_id: int) -> None:
    """Отмечаем статью просмотренной только после успешной отправки в Telegram."""
    ensure_user(user_id)
    with closing(get_connection()) as conn:
        conn.execute(
            "INSERT OR IGNORE INTO delivered_articles (user_id, article_id, delivered_at) "
            "VALUES (?, ?, ?)",
            (user_id, article_id, datetime.now(timezone.utc).isoformat()),
        )
        conn.commit()


def get_random_article() -> sqlite3.Row | None:
    """Запасной вариант: любая статья. Для кнопки «случайная идея» используем choose_random_idea."""
    with closing(get_connection()) as conn:
        return conn.execute(
            "SELECT * FROM articles ORDER BY RANDOM() LIMIT 1"
        ).fetchone()


def load_recent_articles(limit: int = 80) -> list[sqlite3.Row]:
    with closing(get_connection()) as conn:
        return conn.execute(
            """
            SELECT * FROM articles
            ORDER BY
                CASE WHEN published_at IS NULL OR published_at = '' THEN 1 ELSE 0 END,
                published_at DESC,
                id DESC
            LIMIT ?
            """,
            (limit,),
        ).fetchall()


# ---------------------------------------------------------------------------
# RSS
# ---------------------------------------------------------------------------


def parse_published(entry: Any) -> str | None:
    parsed = entry.get("published_parsed") or entry.get("updated_parsed")
    if not parsed:
        return None
    try:
        return datetime(*parsed[:6], tzinfo=timezone.utc).isoformat()
    except Exception:
        return None


def fetch_one_feed(source: dict[str, str]) -> list[dict[str, Any]]:
    """Загружает одну RSS-ленту. Ошибка источника не должна ронять программу."""
    try:
        response = requests.get(
            source["url"],
            timeout=REQUEST_TIMEOUT,
            headers={"User-Agent": USER_AGENT, "Accept": "application/rss+xml, application/xml, text/xml"},
        )
        response.raise_for_status()
        feed = feedparser.parse(response.content)
    except requests.RequestException as exc:
        logger.warning("Не удалось загрузить RSS «%s»: %s", source["name"], exc)
        return []
    except Exception as exc:
        logger.warning("Ошибка разбора RSS «%s»: %s", source["name"], exc)
        return []

    if getattr(feed, "bozo", False) and not feed.entries:
        logger.warning(
            "RSS «%s» выглядит повреждённым: %s",
            source["name"],
            getattr(feed, "bozo_exception", "unknown"),
        )
        return []

    articles: list[dict[str, Any]] = []
    for entry in feed.entries:
        title = clean_rss_text(entry.get("title"))
        link = (entry.get("link") or "").strip()
        if not title or not link:
            continue

        raw_summary = entry.get("summary") or entry.get("description") or ""
        clean = clean_rss_text(raw_summary)
        if not has_meaningful_description(clean):
            # Вместо «XXX» / пустого анонса выберем другую публикацию.
            continue
        summary, detail = pick_summary_and_detail(clean, title=title)
        if not summary:
            # Не показываем незаконченные рекламные или обрезанные описания.
            continue
        guid = (entry.get("id") or link).strip()

        articles.append(
            {
                "guid": f"{source['name']}::{guid}",
                "title": title,
                "summary": summary,
                "detail": detail,
                "url": link,
                "source": source["name"],
                "published_at": parse_published(entry),
            }
        )
        if len(articles) >= MAX_FEED_ITEMS:
            break
    return articles


def fetch_all_feeds() -> list[dict[str, Any]]:
    """Собирает материалы из всех лент. Русские источники идут первыми."""
    collected: list[dict[str, Any]] = []
    seen_urls: set[str] = set()
    ordered = sorted(RSS_SOURCES, key=lambda s: 0 if s.get("lang") == "ru" else 1)
    for source in ordered:
        for article in fetch_one_feed(source):
            if article["url"] in seen_urls:
                continue
            seen_urls.add(article["url"])
            collected.append(article)
    return collected


def persist_articles(articles: list[dict[str, Any]]) -> list[int]:
    ids: list[int] = []
    for article in articles:
        ids.append(save_article(article))
    return ids


def parse_keywords(raw: str) -> list[str]:
    parts = re.split(r"[,;\n]+", raw)
    return [p.strip().lower() for p in parts if p.strip()]


_RU_SUFFIXES = (
    "иями",
    "ями",
    "ами",
    "ого",
    "ему",
    "ыми",
    "ими",
    "ой",
    "ей",
    "ом",
    "ем",
    "ах",
    "ях",
    "ов",
    "ев",
    "ий",
    "ый",
    "ая",
    "ое",
    "ые",
    "ие",
    "ию",
    "ью",
    "ия",
    "ья",
    "ы",
    "и",
    "а",
    "я",
    "у",
    "ю",
    "е",
    "о",
)
_EN_SUFFIXES = ("ation", "tions", "ment", "ings", "ers", "ies", "ing", "ed", "es", "s")


def stem_word(word: str) -> str:
    """Грубая обрезка окончаний: founders → founder, стартапы → стартап."""
    w = re.sub(r"[^\w\-]+", "", (word or "").lower(), flags=re.UNICODE)
    if not w:
        return ""
    suffixes = _RU_SUFFIXES if re.search(r"[а-яё]", w) else _EN_SUFFIXES
    for suf in suffixes:
        if len(w) - len(suf) >= 4 and w.endswith(suf):
            return w[: -len(suf)]
    return w


def expand_keyword(word: str) -> set[str]:
    """Добавляет русские/английские аналоги и простые словоформы."""
    w = (word or "").lower().strip()
    if not w:
        return set()
    found = {w, stem_word(w)}
    for group in KEYWORD_ALIASES:
        stems = {stem_word(item) for item in group}
        if w in group or stem_word(w) in stems:
            found |= set(group)
            found |= stems
    return {item for item in found if item}


def _term_in_text(blob: str, term: str) -> bool:
    if len(term) <= 3:
        return re.search(rf"(?<!\w){re.escape(term)}(?!\w)", blob, flags=re.UNICODE) is not None
    return term in blob


def article_blob(article: sqlite3.Row | dict[str, Any]) -> str:
    return " ".join(
        [
            str(article["title"] or ""),
            str(article["summary"] or ""),
            str(article["detail"] or ""),
        ]
    ).lower()


def matches_interests(article: sqlite3.Row | dict[str, Any], keywords: list[str]) -> bool:
    """Совпадение хотя бы с одним интересом, с учётом двуязычного словаря."""
    if not keywords:
        return True
    blob = article_blob(article)
    for word in keywords:
        if any(_term_in_text(blob, term) for term in expand_keyword(word)):
            return True
    return False


def article_language(article: sqlite3.Row | dict[str, Any]) -> str:
    if is_russian_text(str(article["title"] or "")):
        return "ru"
    source = str(article["source"] or "")
    for item in RSS_SOURCES:
        if item["name"] == source:
            return item.get("lang", "en")
    return "en"


def relevance_score(article: sqlite3.Row | dict[str, Any]) -> int:
    """Простая оценка: идеи / кейсы / стартапы минус посторонние темы."""
    blob = article_blob(article)
    score = 0
    if article_language(article) == "ru":
        score += 6
    if any(mark in blob for mark in IDEA_MARKERS):
        score += 4
    if any(mark in blob for mark in CASE_MARKERS):
        score += 4
    if any(mark in blob for mark in STARTUP_MARKERS):
        score += 3
    if any(mark in blob for mark in GENERAL_BIZ_MARKERS):
        score += 2
    if any(mark in blob for mark in NEGATIVE_MARKERS):
        score -= 8
    return score


def normalized_title(title: str) -> str:
    """Убирает регистр и знаки препинания для сравнения заголовков."""
    return re.sub(r"\s+", " ", re.sub(r"[^\w\s]", " ", title.casefold())).strip()


def canonical_url(url: str) -> str:
    """Ссылка без рекламных UTM-параметров для отсечения одинаковых статей."""
    parts = urlsplit(url.strip())
    params = [
        (key, value) for key, value in parse_qsl(parts.query, keep_blank_values=True)
        if not key.lower().startswith("utm_") and key.lower() not in {"fbclid", "gclid"}
    ]
    return urlunsplit((parts.scheme.lower(), parts.netloc.lower(),
                       parts.path.rstrip("/"), urlencode(params), ""))


def choose_digest(
    keywords: list[str],
    limit: int = DIGEST_MAX,
    exclude_ids: set[int] | None = None,
) -> list[sqlite3.Row]:
    """Свежие уникальные материалы: сначала русские и релевантные бизнесу."""
    recent = load_recent_articles(limit=220)
    scored: list[tuple[int, str, sqlite3.Row]] = []
    seen: set[int] = set()
    seen_urls: set[str] = set()
    seen_titles: set[str] = set()
    excluded = exclude_ids or set()
    for article in recent:
        aid = int(article["id"])
        if aid in seen or aid in excluded:
            continue
        seen.add(aid)
        link_key = canonical_url(str(article["url"]))
        title_key = normalized_title(str(article["title"]))
        if link_key in seen_urls or title_key in seen_titles:
            continue
        seen_urls.add(link_key)
        seen_titles.add(title_key)
        # В SQLite могли остаться заглушки из предыдущей версии бота.
        if not has_meaningful_description(str(article["summary"] or "")):
            continue
        if not matches_interests(article, keywords):
            continue
        score = relevance_score(article)
        if score < MIN_DIGEST_SCORE:
            continue
        scored.append((score, article_language(article), article))

    russian = sorted([row for row in scored if row[1] == "ru"], key=lambda x: -x[0])
    english = sorted([row for row in scored if row[1] != "ru"], key=lambda x: -x[0])

    picked: list[sqlite3.Row] = []
    for _, _, article in russian:
        picked.append(article)
        if len(picked) >= limit:
            return picked

    # Английские добавляем только если своих не хватило — и не больше DIGEST_MIN.
    if len(picked) < DIGEST_MIN:
        for _, _, article in english:
            picked.append(article)
            if len(picked) >= DIGEST_MIN:
                break
    return picked


def choose_random_idea(exclude_ids: set[int] | None = None) -> sqlite3.Row | None:
    """Случайная идея из уже собранных новостей с высокой бизнес-оценкой."""
    recent = load_recent_articles(limit=220)
    strong: list[tuple[int, sqlite3.Row]] = []
    fallback: list[tuple[int, sqlite3.Row]] = []
    for article in recent:
        if not has_meaningful_description(str(article["summary"] or "")):
            continue
        score = relevance_score(article)
        fallback.append((score, article))
        if score >= MIN_RANDOM_SCORE:
            strong.append((score, article))
    pool = strong or sorted(fallback, key=lambda x: -x[0])[:15]
    if not pool:
        return None  # Не возвращаем статью-заглушку даже в крайнем случае.
    # Сначала новые идеи; когда база исчерпана, случайную идею можно повторить.
    unseen = [(s, a) for s, a in pool if int(a["id"]) not in (exclude_ids or set())]
    pool = unseen or pool
    russian_pool = [(s, a) for s, a in pool if article_language(a) == "ru"]
    chosen = russian_pool or pool
    weights = [max(1, item[0]) for item in chosen]
    return random.choices([item[1] for item in chosen], weights=weights, k=1)[0]


# ---------------------------------------------------------------------------
# Оформление сообщений
# ---------------------------------------------------------------------------


def format_article_html(article: sqlite3.Row | dict[str, Any], intro: str | None = None) -> str:
    """Компактная карточка без ссылки в тексте — оригинал открывается кнопкой."""
    title = html_escape(str(article["title"]))
    source = html_escape(str(article["source"]))
    raw_summary = str(article["summary"] or "").strip()
    raw_detail = str(article["detail"] or "").strip()
    summary_text = complete_excerpt(raw_summary)
    detail_text = complete_excerpt(raw_detail, limit=DETAIL_LIMIT, max_sentences=1)
    if redundant_detail(raw_summary, raw_detail) or redundant_detail(summary_text, detail_text):
        detail_text = ""
    summary = html_escape(summary_text) if summary_text else ""
    detail = html_escape(detail_text) if detail_text else ""

    lines: list[str] = []
    lines.append(f"🐦 {html_escape(intro or next_intro())}")
    lines.append("")
    lines.append(f"💡 <b>{title}</b>")
    if summary:
        lines.append("")
        lines.append(summary)
    if not summary:
        # Например, если пользователь раньше сохранил новость с «XXX».
        lines.append("")
        lines.append("Краткого описания нет — подробности по кнопке «Читать оригинал».")
    if detail:
        lines.append("")
        lines.append("🔥 <b>В чём интерес?</b>")
        lines.append(detail)
    lines.append("")
    lines.append(f"📰 Источник: {source}")
    return "\n".join(lines)


def article_keyboard(article_id: int, url: str, saved: bool = False) -> InlineKeyboardMarkup:
    save_btn = (
        InlineKeyboardButton("🗑 Убрать из гнезда", callback_data=f"unsave:{article_id}")
        if saved
        else InlineKeyboardButton("⭐ В гнездо", callback_data=f"save:{article_id}")
    )
    return InlineKeyboardMarkup(
        [
            [
                save_btn,
                InlineKeyboardButton("🔗 Читать оригинал", url=url),
            ]
        ]
    )


# ---------------------------------------------------------------------------
# Обработчики Telegram
# ---------------------------------------------------------------------------


async def start(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not update.message:
        return
    ensure_user(update.effective_user.id)
    context.user_data[AWAITING_INTERESTS] = False
    await update.message.reply_text(
        WELCOME_TEXT,
        reply_markup=MAIN_KEYBOARD,
    )


async def help_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.message:
        return
    text = (
        "Я Кейсорока. Вот что умею:\n\n"
        "/digest — свежая подборка находок\n"
        "/random — случайная идея\n"
        "/saved — твоё гнездо (избранное)\n"
        "/interests — ключевые слова для фильтра\n"
        "/start — снова показать меню\n\n"
        "Рассылку можно включить и выключить кнопкой «🔔 Настройка рассылки»."
    )
    await update.message.reply_text(text, reply_markup=MAIN_KEYBOARD)


async def refresh_feeds() -> list[int]:
    """Загрузка RSS в отдельном потоке, чтобы не блокировать ответы бота."""
    articles = await asyncio.to_thread(fetch_all_feeds)
    if not articles:
        return []
    return await asyncio.to_thread(persist_articles, articles)


async def send_digest_to_chat(
    bot: Any,
    chat_id: int,
    user_id: int,
    is_daily: bool = False,
    allow_seen: bool = False,
) -> None:
    user = get_user(user_id)
    keywords = parse_keywords(user["interests"] if user else "")

    await asyncio.to_thread(ensure_user, user_id)
    saved_ids = await refresh_feeds()
    if articles_count() == 0 and not saved_ids:
        await bot.send_message(
            chat_id=chat_id,
            text="Кар-р… Сегодня ленты молчат. Попробуй ещё раз чуть позже.",
            reply_markup=MAIN_KEYBOARD,
        )
        return

    exclude_ids = set() if allow_seen else await asyncio.to_thread(delivered_article_ids, user_id)
    items = await asyncio.to_thread(choose_digest, keywords, DIGEST_MAX, exclude_ids)
    if not items and exclude_ids and await asyncio.to_thread(choose_digest, keywords, 1):
        # Это уже показанные статьи, не ошибка источников или интересов.
        if not is_daily:
            await bot.send_message(
                chat_id=chat_id,
                text="Кар-р! Все подходящие находки я тебе уже показывала. "
                     "Новых пока нет. Могу повторить старую подборку по твоему желанию.",
                reply_markup=InlineKeyboardMarkup([[
                    InlineKeyboardButton("🔄 Показать старые", callback_data="digest:repeat")
                ]]),
            )
        return
    if not items and keywords:
        await bot.send_message(
            chat_id=chat_id,
            text=random.choice(EMPTY_DIGEST_PHRASES),
            reply_markup=interests_keyboard(True),
        )
        return
    if not items:
        await bot.send_message(
            chat_id=chat_id,
            text="Пока нечего показать по деловой теме. Загляни позже — я ещё полетаю по лентам.",
            reply_markup=MAIN_KEYBOARD,
        )
        return

    prefix = "Ежедневная почта от Кейсороки.\n\n" if is_daily else ""
    await bot.send_message(
        chat_id=chat_id,
        text=prefix + random.choice(DIGEST_INTROS),
        reply_markup=MAIN_KEYBOARD,
        disable_web_page_preview=True,
    )

    for article in items:
        try:
            await bot.send_message(
                chat_id=chat_id,
                text=format_article_html(article, intro=next_intro()),
                parse_mode=ParseMode.HTML,
                disable_web_page_preview=True,
                reply_markup=article_keyboard(int(article["id"]), str(article["url"])),
            )
            await asyncio.to_thread(mark_delivered, user_id, int(article["id"]))
        except TelegramError as exc:
            logger.error("Не удалось отправить материал %s: %s", article["id"], exc)


async def digest_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not update.message:
        return
    await update.message.reply_text("Лечу за свежими находками, подожди секунду…")
    await send_digest_to_chat(
        context.bot,
        update.effective_chat.id,
        update.effective_user.id,
    )


async def random_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not update.message:
        return
    if articles_count() == 0:
        await update.message.reply_text("Гнездо пока пустое — сначала соберу новости.")
        await refresh_feeds()

    seen_ids = await asyncio.to_thread(delivered_article_ids, update.effective_user.id)
    article = await asyncio.to_thread(choose_random_idea, seen_ids)
    if not article:
        await update.message.reply_text(
            "Кар-р, пока не нашла достаточно содержательных бизнес-материалов. Попробуй /digest позже.",
            reply_markup=MAIN_KEYBOARD,
        )
        return

    await update.message.reply_text(
        format_article_html(article, intro=next_intro()),
        parse_mode=ParseMode.HTML,
        disable_web_page_preview=True,
        reply_markup=article_keyboard(int(article["id"]), str(article["url"])),
    )
    await asyncio.to_thread(mark_delivered, update.effective_user.id, int(article["id"]))


def interests_text(raw: str) -> str:
    words = parse_keywords(raw)
    if not words:
        return (
            "Сейчас я приношу всё подряд: идеи, кейсы и стартапы.\n\n"
            "Напиши ключевые слова через запятую, например:\n"
            "маркетинг, стартапы, ритейл, франшиза, подписка\n\n"
            "Или выбери готовую отрасль кнопкой «🏢 Выбрать отрасль»."
        )
    listed = ", ".join(words)
    return (
        f"Сейчас ищу по словам: {listed}\n\n"
        "Напиши новый список через запятую — я заменю старый.\n"
        "Или выбери готовую отрасль, или очисти интересы для всех тем."
    )


def interests_keyboard(has_interests: bool) -> InlineKeyboardMarkup:
    rows = [
        [InlineKeyboardButton("✏️ Изменить список", callback_data="interests:edit")],
        [InlineKeyboardButton("🏢 Выбрать отрасль", callback_data="interests:industries")],
    ]
    if has_interests:
        rows.append([InlineKeyboardButton("🧹 Очистить интересы", callback_data="interests:clear")])
    return InlineKeyboardMarkup(rows)


def industry_keyboard() -> InlineKeyboardMarkup:
    """Выбор одной отрасли; ручной ввод интересов остаётся доступным."""
    rows = [
        [InlineKeyboardButton(label, callback_data=f"industry:{key}")]
        for key, (label, _) in INDUSTRIES.items()
    ]
    rows.append([InlineKeyboardButton("↩️ Назад к интересам", callback_data="interests:view")])
    return InlineKeyboardMarkup(rows)


async def interests_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not update.message:
        return
    ensure_user(update.effective_user.id)
    user = get_user(update.effective_user.id)
    raw = user["interests"] if user else ""
    await update.message.reply_text(
        interests_text(raw),
        reply_markup=interests_keyboard(bool(parse_keywords(raw))),
    )


async def saved_command(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not update.message:
        return
    ensure_user(update.effective_user.id)
    items = list_favorites(update.effective_user.id)
    if not items:
        await update.message.reply_text(
            "Гнездо пустое. Когда что-то зацепит — жми «⭐ В гнездо».",
            reply_markup=MAIN_KEYBOARD,
        )
        return

    await update.message.reply_text(
        f"В гнезде {len(items)} материал(ов). Забирай, пригодится!",
        reply_markup=MAIN_KEYBOARD,
    )
    for article in items:
        await update.message.reply_text(
            format_article_html(article),
            parse_mode=ParseMode.HTML,
            disable_web_page_preview=True,
            reply_markup=article_keyboard(
                int(article["id"]),
                str(article["url"]),
                saved=True,
            ),
        )


async def digest_settings(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    if not update.effective_user or not update.message:
        return
    ensure_user(update.effective_user.id)
    user = get_user(update.effective_user.id)
    enabled = bool(user["digest_enabled"]) if user else True
    tz_name = os.getenv("TIMEZONE", "Europe/Moscow")
    digest_time = os.getenv("DIGEST_TIME", "09:00")
    status = "включена" if enabled else "выключена"
    text = (
        f"Ежедневная рассылка сейчас {status}.\n"
        f"Время: {digest_time} ({tz_name}).\n\n"
        "Я приношу дайджест, пока программа запущена. "
        "Если выключишь ноутбук — рассылка подождёт следующего полёта."
    )
    button = (
        InlineKeyboardButton("🔕 Выключить рассылку", callback_data="digest:off")
        if enabled
        else InlineKeyboardButton("🔔 Включить рассылку", callback_data="digest:on")
    )
    await update.message.reply_text(
        text,
        reply_markup=InlineKeyboardMarkup([[button]]),
    )


async def on_menu_button(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    """Обрабатывает кнопки главного меню и ввод ключевых слов."""
    if not update.message or not update.effective_user:
        return

    text = (update.message.text or "").strip()

    if context.user_data.get(AWAITING_INTERESTS):
        if text in {BTN_DIGEST, BTN_RANDOM, BTN_SAVED, BTN_INTERESTS, BTN_DIGEST_SETTINGS}:
            context.user_data[AWAITING_INTERESTS] = False
        else:
            words = parse_keywords(text)
            set_interests(update.effective_user.id, ", ".join(words))
            context.user_data[AWAITING_INTERESTS] = False
            if words:
                await update.message.reply_text(
                    f"Запомнила: {', '.join(words)}. Теперь буду приносить ближе к теме.",
                    reply_markup=MAIN_KEYBOARD,
                )
            else:
                await update.message.reply_text(
                    "Список пустой — снова несу всё подряд.",
                    reply_markup=MAIN_KEYBOARD,
                )
            return

    mapping = {
        BTN_DIGEST: digest_command,
        BTN_RANDOM: random_command,
        BTN_SAVED: saved_command,
        BTN_INTERESTS: interests_command,
        BTN_DIGEST_SETTINGS: digest_settings,
    }
    handler = mapping.get(text)
    if handler:
        await handler(update, context)
        return

    await update.message.reply_text(
        "Не узнала эту команду. Нажми кнопку меню или /help.",
        reply_markup=MAIN_KEYBOARD,
    )


async def on_callback(update: Update, context: ContextTypes.DEFAULT_TYPE) -> None:
    query = update.callback_query
    if not query or not update.effective_user:
        return
    await query.answer()

    data = query.data or ""
    user_id = update.effective_user.id

    if data.startswith("save:"):
        article_id = int(data.split(":", 1)[1])
        article = get_article(article_id)
        if not article:
            await query.answer("Материал уже улетел.", show_alert=True)
            return
        added = add_favorite(user_id, article_id)
        note = "Уже в гнезде!" if not added else "Забрала в гнездо. Пригодится!"
        try:
            await query.edit_message_reply_markup(
                reply_markup=article_keyboard(article_id, str(article["url"]), saved=True)
            )
        except TelegramError:
            pass
        await context.bot.send_message(chat_id=query.message.chat_id, text=note)
        return

    if data.startswith("unsave:"):
        article_id = int(data.split(":", 1)[1])
        article = get_article(article_id)
        remove_favorite(user_id, article_id)
        if article:
            try:
                await query.edit_message_reply_markup(
                    reply_markup=article_keyboard(article_id, str(article["url"]), saved=False)
                )
            except TelegramError:
                pass
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="Убрала из гнезда. Если передумаешь — снова жми звезду.",
        )
        return

    if data == "interests:industries":
        await query.edit_message_text(
            "🐦 Какую отрасль тебе принести в гнездо?\n\n"
            "Выбери одно направление — я настрою ключевые слова за тебя. "
            "Текущий список интересов заменится. Свои слова можно будет ввести позже.",
            reply_markup=industry_keyboard(),
        )
        return

    if data == "interests:view":
        user = get_user(user_id)
        raw = user["interests"] if user else ""
        await query.edit_message_text(
            interests_text(raw),
            reply_markup=interests_keyboard(bool(parse_keywords(raw))),
        )
        return

    if data.startswith("industry:"):
        industry_key = data.partition(":")[2]
        industry = INDUSTRIES.get(industry_key)
        if industry is None:
            await context.bot.send_message(
                chat_id=query.message.chat_id,
                text="Не узнала эту отрасль. Открой «🔎 Мои интересы» и попробуй ещё раз.",
            )
            return
        label, keywords = industry
        set_interests(user_id, keywords)
        context.user_data[AWAITING_INTERESTS] = False
        await query.edit_message_text(
            f"Кар-р! Выбрала {label}. 🐦\n\n"
            "Теперь «📰 Свежие находки» будут подбираться по этой отрасли. "
            "Если публикаций пока нет, попробуй другое направление.\n\n"
            "Свои ключевые слова всегда можно задать через «✏️ Изменить список».",
            reply_markup=interests_keyboard(True),
        )
        return

    if data == "interests:edit":
        context.user_data[AWAITING_INTERESTS] = True
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="Пиши ключевые слова через запятую. Я жду одно сообщение.",
        )
        return

    if data == "interests:clear":
        set_interests(user_id, "")
        context.user_data[AWAITING_INTERESTS] = False
        await context.bot.send_message(
            chat_id=query.message.chat_id,
            text="Интересы очищены. Снова приношу находки по всем направлениям.",
            reply_markup=MAIN_KEYBOARD,
        )
        return

    if data == "digest:repeat":
        # Повторы только по явному запросу пользователя.
        await send_digest_to_chat(
            context.bot, chat_id=query.message.chat_id, user_id=user_id, allow_seen=True
        )
        return

    if data == "digest:off":
        set_digest_enabled(user_id, False)
        await query.edit_message_text(
            "Рассылку выключила. Если соскучишься — включи снова в меню."
        )
        return

    if data == "digest:on":
        set_digest_enabled(user_id, True)
        tz_name = os.getenv("TIMEZONE", "Europe/Moscow")
        digest_time = os.getenv("DIGEST_TIME", "09:00")
        await query.edit_message_text(
            f"Рассылка снова включена. Буду стучаться около {digest_time} ({tz_name}), "
            "пока программа запущена."
        )
        return


async def daily_digest_job(context: ContextTypes.DEFAULT_TYPE) -> None:
    """Ежедневная рассылка всем, кто её не отключал."""
    users = list_digest_users()
    logger.info("Ежедневная рассылка: получателей %s", len(users))
    for user in users:
        try:
            await send_digest_to_chat(
                context.bot,
                chat_id=int(user["telegram_id"]),
                user_id=int(user["telegram_id"]),
                is_daily=True,
            )
        except TelegramError as exc:
            logger.error("Не удалось отправить рассылку пользователю %s: %s", user["telegram_id"], exc)
        except Exception:
            logger.exception("Сбой рассылки для пользователя %s", user["telegram_id"])


async def error_handler(update: object, context: ContextTypes.DEFAULT_TYPE) -> None:
    logger.exception("Необработанная ошибка при обработке обновления")


def setup_logging() -> None:
    logging.basicConfig(
        level=logging.INFO,
        format="%(asctime)s [%(levelname)s] %(name)s: %(message)s",
    )
    # Токен не должен попадать в логи сторонних библиотек.
    logging.getLogger("httpx").setLevel(logging.WARNING)
    logging.getLogger("httpcore").setLevel(logging.WARNING)


def build_application(token: str) -> Application:
    application = Application.builder().token(token).build()

    application.add_handler(CommandHandler("start", start))
    application.add_handler(CommandHandler("help", help_command))
    application.add_handler(CommandHandler("digest", digest_command))
    application.add_handler(CommandHandler("random", random_command))
    application.add_handler(CommandHandler("interests", interests_command))
    application.add_handler(CommandHandler("saved", saved_command))
    application.add_handler(CallbackQueryHandler(on_callback))
    application.add_handler(MessageHandler(filters.TEXT & ~filters.COMMAND, on_menu_button))
    application.add_error_handler(error_handler)

    tz_name = os.getenv("TIMEZONE", "Europe/Moscow")
    try:
        tz = ZoneInfo(tz_name)
    except Exception:
        logger.warning("Неизвестный TIMEZONE=%s, использую Europe/Moscow", tz_name)
        tz = ZoneInfo("Europe/Moscow")

    digest_clock = parse_digest_time(os.getenv("DIGEST_TIME", "09:00"))
    job_time = dt_time(
        hour=digest_clock.hour,
        minute=digest_clock.minute,
        tzinfo=tz,
    )
    if application.job_queue is None:
        logger.error("JobQueue недоступна. Установите python-telegram-bot[job-queue].")
    else:
        application.job_queue.run_daily(daily_digest_job, time=job_time, name="daily_digest")
        logger.info("Рассылка запланирована на %s (%s)", job_time.strftime("%H:%M"), tz.key)

    return application


def main() -> None:
    setup_logging()
    load_dotenv()

    token = (os.getenv("BOT_TOKEN") or "").strip()
    if not token or token == "your_telegram_bot_token":
        print(
            "BOT_TOKEN не задан.\n"
            "Скопируй .env.example в .env и вставь токен от @BotFather.\n"
            "Бот специально не запускается без токена."
        )
        sys.exit(0)

    init_db()
    application = build_application(token)
    logger.info("Кейсорока взлетает…")
    application.run_polling(drop_pending_updates=True)


if __name__ == "__main__":
    main()
