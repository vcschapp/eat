use std::error::Error;
use std::io::Read;

// TODO: Delete
pub fn add(left: u64, right: u64) -> u64 {
    left + right
}

/// Opening brace, the JSON separator that denotes the start an object value.
pub static SEP_BRACE_O: char = '{';

/// Closing brace, the JSON separator that denotes the end of an object value.
pub static SEP_BRACE_C: char = '}';

/// Opening bracket, the JSON separator that denotes the start of an array value.
pub static SEP_BRACK_O: char = '[';

/// Closing bracket, the JSON separator that denotes the end of an array value.
pub static SEP_BRACK_C: char = ']';

/// Comma, the JSON separator that appears between the members of objects and arrays.
pub static SEP_COMMA: char = ',';

/// Colon, the JSON separator that appears between the key and value parts of an object member.
pub static SEP_COLON: char = ':';

/// JSON keyword `false`.
pub static KEY_FALSE: &str = "false";

/// JSON keyword `true`.
pub static KEY_TRUE: &str = "true";

/// JSON keyword `null`.
pub static KEY_NULL: &str = "null";

/// Position of token or error within a JSON input stream. This position is relative to the start of
/// the [Stream], not the [Buf].
#[derive(Default, Clone, Copy)]
struct Pos {
    pub byte_off: u64,
    pub char_off: u64,
    pub line: u64,
    pub col: u64,
}

// Category of JSON error.
pub enum JSONErrorCat {
    /// Lexical error. May be produced either type of [Stream], [Lex] or
    /// [Syn].
    Lex,
    /// Syntactic error. Only produced by [Syn], as a [Lex] does not
    /// check JSON syntax.
    Syn,
}

/// Error representing invalid JSON.
pub struct JSONError {
    pub cat: JSONErrorCat,
    pub pos: Pos,
}

impl Error for JSONError {
    // TODO - Implement std::error::Error so cause information can be
    // tracked for things like unexpected EOF.
}

/// A JSON token read from a [Buf].
pub enum Tok<'a> {
    /// Separator token.
    ///
    /// Contains the separator literally as it appears in the JSON input. May have one of six
    /// possible values:
    /// - [SEP_BRACE_O]
    /// - [SEP_BRACE_C]
    /// - [SEP_BRACK_O]
    /// - [SEP_BRACK_C]
    /// - [SEP_COMMA]
    /// - [SEP_COLON]
    Sep(char),

    /// Number token.
    ///
    /// Contains the number value literally as it appears in the JSON input.
    Num(&'a str),

    /// String token.
    ///
    /// Contains the string value literally as it appears in the JSON input, including the opening
    /// and closing double quotation mark (`"`).
    ///
    /// Examples: `""`, `"foo"`
    Str(&'a str),

    /// Keyword token.
    ///
    /// Contains the keyword literally as it appears in the JSON input. May have one of three
    /// possible values:
    /// - [KEY_FALSE]
    /// - [KEY_TRUE]
    /// - [KEY_NULL]
    Key(&'static str),

    /// End of usable input tokens.
    ///
    /// After all usable input has been consumed in the buffer, there may still be more unusable
    /// input in the form of partial tokens. This unusable remainder, if any, is included with the
    /// token.
    End(&'a str),

    /// Error token.
    ///
    /// Indicates that a lexical or syntactic error was detected. Includes the error details,
    /// including its position within the buffer.
    Err(JSONError),
}

pub trait Stream<'a> {
    // TODO: Need a way to indicate no more bufs!
    fn next(&mut self) -> Option<&'a impl Buf>;
    fn pos(&self) -> Pos;
}

pub trait Buf: Drop {
    fn next(&mut self) -> Tok;
    fn pos(&self) -> Pos;
}

pub struct Lex<'a, R>
where
    R: Read,
{
    reader: R,
    pos: Pos,
    buf: Option<LexBuf>,
}

impl<'a, R> Lex<'a, R>
where
    R: Read,
{
    fn builder() -> LexBuilder<R> {
        LexBuilder { reader: None }
    }
}

struct LexBuilder<R>
where
    R: Read,
{
    reader: Option<R>,
}

impl<R> LexBuilder<R>
where
    R: Read,
{
    pub fn reader(mut self, reader: R) -> Self {
        self.reader = Some(reader);
        self
    }

    pub fn build(self) -> Lex<R> {
        Lex {
            reader: self.reader.expect("reader not provided"),
            pos: Pos::default(),
        }
    }
}

impl<R> Stream for Lex<R>
where
    R: Read,
{
    fn next(&mut self) -> Option<impl Buf> {
        // Logic:
        // 1) If there is a buffer out in use, we panic and say it needs to be
        //    returned.
        // 2) If there is no buffer at all, we have to allocate it.
        // 3) Upon being returned (elsewhere), if buffer was NOT fully used then
        //    we are quietly put into an error state that will trigger a panic
        //    here. If it was fully used, then incomplete remainder is now copied
        //    to the front of the buffer. If incomplete remaindert WAS at the
        //    front of the buffer, then we have to allocate a bigger buffer.
    }

    fn pos(&self) -> Pos {
        self.pos
    }
}

struct LexBuf {}

impl LexBuf {}

impl Buf for LexBuf {}

pub struct Syn<R>
where
    R: Read,
{
    lex: Lex<R>,
}

impl<R> Syn<R>
where
    R: Read,
{
    fn builder() -> SynBuilder<R> {
        SynBuilder { lex: None }
    }
}

struct SynBuilder<R>
where
    R: Read,
{
    lex: Option<Lex<R>>,
}

impl<R> SynBuilder<R>
where
    R: Read,
{
    pub fn reader(mut self, lex: Lex<R>) -> Self {
        self.lex = Some(lex);
        self
    }

    pub fn build(self) -> Syn<R> {}
}

impl Stream for Syn {
    fn next(&mut self) -> Option<impl Buf> {}

    fn pos(&self) -> Pos {
        self.pos
    }
}

struct SynBuf {}

impl Buf for SynBuf {}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn it_works() {
        let result = add(2, 2);
        assert_eq!(result, 4);
    }
}
