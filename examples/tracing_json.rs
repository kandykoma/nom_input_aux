use nom_input_aux::{InputAux, context};

use nom::{
  branch::alt,
  bytes::complete::{escaped, tag, take_while},
  character::complete::{alphanumeric1 as alphanumeric, char, one_of},
  combinator::{cut, map, opt, value},
  error::{convert_error, ContextError, ErrorKind, ParseError, VerboseError, FromExternalError},
  multi::separated_list0,
  number::complete::double,
  sequence::{delimited, preceded, separated_pair, terminated},
  Err, IResult,
};
use std::collections::HashMap;
use std::str;

#[derive(Debug, PartialEq)]
pub enum JsonValue {
  Str(String),
  Boolean(bool),
  Num(f64),
  Array(Vec<JsonValue>),
  Object(HashMap<String, JsonValue>),
}

fn sp<'a, E: ParseError<InputAux<Tracer, &'a str>>>(i: InputAux<Tracer, &'a str>) -> IResult<InputAux<Tracer, &'a str>, InputAux<Tracer, &'a str>, E> {
  let chars = " \t\r\n";

  take_while(move |c| chars.contains(c))(i)
}

fn parse_str<'a, E: ParseError<InputAux<Tracer, &'a str>>>(i: InputAux<Tracer, &'a str>) -> IResult<InputAux<Tracer, &'a str>, InputAux<Tracer, &'a str>, E> {
  escaped(alphanumeric, '\\', one_of("\"n\\"))(i)
}

fn boolean<'a, E: ParseError<InputAux<Tracer, &'a str>>>(input: InputAux<Tracer, &'a str>) -> IResult<InputAux<Tracer, &'a str>, bool, E> {
  let parse_true = value(true, tag("true"));

  let parse_false = value(false, tag("false"));

  alt((parse_true, parse_false))(input)
}

fn string<'a, E: FromExternalError<InputAux<Tracer, &'a str>, String> + ParseError<InputAux<Tracer, &'a str>> + ContextError<InputAux<Tracer, &'a str>>>(
  i: InputAux<Tracer, &'a str>,
) -> IResult<InputAux<Tracer, &'a str>, InputAux<Tracer, &'a str>, E> {
  context(
    "string",
    preceded(char('\"'), cut(terminated(parse_str, char('\"')))),
  )(i)
}

fn array<'a, E: FromExternalError<InputAux<Tracer, &'a str>, String> + ParseError<InputAux<Tracer, &'a str>> + ContextError<InputAux<Tracer, &'a str>>>(
  i: InputAux<Tracer, &'a str>,
) -> IResult<InputAux<Tracer, &'a str>, Vec<JsonValue>, E> {
  context(
    "array",
    preceded(
      char('['),
      cut(terminated(
        separated_list0(preceded(sp, char(',')), json_value),
        preceded(sp, char(']')),
      )),
    ),
  )(i)
}

fn key_value<'a, E: FromExternalError<InputAux<Tracer, &'a str>, String> + ParseError<InputAux<Tracer, &'a str>> + ContextError<InputAux<Tracer, &'a str>>>(
  i: InputAux<Tracer, &'a str>,
) -> IResult<InputAux<Tracer, &'a str>, (InputAux<Tracer, &'a str>, JsonValue), E> {
  separated_pair(
    preceded(sp, string),
    cut(preceded(sp, char(':'))),
    json_value,
  )(i)
}

fn hash<'a, E: FromExternalError<InputAux<Tracer, &'a str>, String> + ParseError<InputAux<Tracer, &'a str>> + ContextError<InputAux<Tracer, &'a str>>>(
  i: InputAux<Tracer, &'a str>,
) -> IResult<InputAux<Tracer, &'a str>, HashMap<String, JsonValue>, E> {
  context(
    "map",
    preceded(
      char('{'),
      cut(terminated(
        map(
          separated_list0(preceded(sp, char(',')), key_value),
          |tuple_vec| {
            tuple_vec
              .into_iter()
              .map(|(k, v)| (String::from(k.input), v))
              .collect()
          },
        ),
        preceded(sp, char('}')),
      )),
    ),
  )(i)
}

fn json_value<'a, E: FromExternalError<InputAux<Tracer, &'a str>, String> + ParseError<InputAux<Tracer, &'a str>> + ContextError<InputAux<Tracer, &'a str>>>(
  i: InputAux<Tracer, &'a str>,
) -> IResult<InputAux<Tracer, &'a str>, JsonValue, E> {
  preceded(
    sp,
    alt((
      map(hash, JsonValue::Object),
      map(array, JsonValue::Array),
      map(string, |s| JsonValue::Str(String::from(s.input))),
      map(double, JsonValue::Num),
      map(boolean, JsonValue::Boolean),
    )),
  )(i)
}

fn root<'a, E: FromExternalError<InputAux<Tracer, &'a str>, String> + ParseError<InputAux<Tracer, &'a str>> + ContextError<InputAux<Tracer, &'a str>>>(
  i: InputAux<Tracer, &'a str>,
) -> IResult<InputAux<Tracer, &'a str>, JsonValue, E> {
  delimited(
    sp,
    alt((map(hash, JsonValue::Object), map(array, JsonValue::Array))),
    opt(sp),
  )(i)
}

#[derive(Debug, Clone, Copy)]
struct Tracer{array: i32, object: i32, limit: i32, depth: i32}
impl Tracer {
  fn new(limit: i32) -> Self {
    Tracer{array: 0, object: 0, limit, depth: 0}
  }
}
impl nom_input_aux::ContextAware<String> for Tracer {
  fn push_context(&mut self, context: &'static str) -> Option<Result<String, String>> {
    match context {
      "array" => { println!("entering array {}", self.depth); self.array += 1; },
      "map" => { println!("entering object {}", self.depth); self.object += 1; },
      s => { println!("entering other: {} {}", self.depth, s); },
    };
    self.depth += 1;
    if self.array + self.object > self.limit {
      Some(Err("too deep".to_string()))
    } else {
      None
    }
  }
  fn pop_context<I, O, E: nom::error::FromExternalError<I, String>>(&mut self, res: &nom::IResult<I, O, E>) -> Option<Result<String, String>> {
    self.depth -= 1;
    println!("leaving {} {}", self.depth, res.is_ok());
    None
  }
}
fn main() {
  let data = "  { \"a\"\t: 42,
  \"b\": [ \"x\", \"y\", 12 ] ,
  \"c\": { \"hello\" : \"world\"
  }
  } ";

  println!(
    "will try to parse valid JSON data:\n\n**********\n{}\n**********\n",
    data
  );

  println!(
    "parsing a valid file:\n{:#?}\n",
    root::<(_, ErrorKind)>(InputAux{aux: Tracer::new(100), input: data})
  );
  println!(
    "parsing a valid file with limit:\n{:#?}\n",
    root::<(_, ErrorKind)>(InputAux{aux: Tracer::new(2), input: data})
  );

  let data = InputAux{aux: Tracer::new(100), input: "  { \"a\"\t: 42,
  \"b\": [ \"x\", \"y\", 12 ] ,
  \"c\": { 1\"hello\" : \"world\"
  }
  } "};

  println!(
    "will try to parse invalid JSON data:\n\n**********\n{:?}\n**********\n",
    data
  );

  println!(
    "basic errors - `root::<(&str, ErrorKind)>(data)`:\n{:#?}\n",
    root::<(_, ErrorKind)>(data)
  );

  println!("parsed verbose: {:#?}", root::<VerboseError<_>>(data));

  match root::<VerboseError<_>>(data) {
    Err(Err::Error(e)) | Err(Err::Failure(e)) => {
      println!(
        "verbose errors - `root::<VerboseError>(data)`:\n{:?}",
        convert_error(data, e)
      );
    }
    _ => {}
  }
}
