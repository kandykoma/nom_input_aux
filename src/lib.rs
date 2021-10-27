use std::ops::{
	Range,
	RangeFrom,
	RangeFull,
	RangeTo,
};
use std::str::FromStr;

use nom::{
	AsBytes,
	Compare,
	CompareResult,
	Err,
	FindSubstring,
	FindToken,
	InputIter,
	InputLength,
	InputTake,
	InputTakeAtPosition,
	Needed,
	Offset,
	ParseTo,
	Slice,
};
use nom::error::{
	ErrorKind,
	ParseError,
};

/// Struct to carry auxiliary data along with the input.
#[derive(Debug, Clone)]
pub struct InputAux<Aux, I> {
	/// Auxiliary data for the parsing logic.
	pub aux: Aux,

	/// Input to parse.
	pub input: I
}

impl<Aux, I> InputAux<Aux, I> {
	/// Create a new instance.
	pub fn new(aux: Aux, buf: I) -> Self {
		InputAux{aux, input: buf}
	}
}

pub trait ContextAware<EE> {
	// return None if successfully entered context, return Some(Ok()) if an error is to be signaled or Some(Err()) if a failure.
	fn push_context(&mut self, context: &'static str) -> Option<Result<EE, EE>>;
	fn pop_context<I, O, E: nom::error::FromExternalError<I, EE>>(&mut self, res: &nom::IResult<I, O, E>) -> Option<Result<EE, EE>>;
}

pub fn context<EE, Aux: Clone + ContextAware<EE>, I: Clone, E: nom::error::FromExternalError<InputAux<Aux, I>, EE> + nom::error::ContextError<InputAux<Aux, I>>, F, O>(
	ctxt: &'static str,
	mut f: F,
) -> impl FnMut(InputAux<Aux, I>) -> nom::IResult<InputAux<Aux, I>, O, E>
where
	F: nom::Parser<InputAux<Aux, I>, O, E>,
{
	move |mut i: InputAux<Aux, I>| {
		match i.aux.push_context(ctxt) {
			None => (),
			Some(Ok(e)) => return Err(Err::Error(E::from_external_error(i, ErrorKind::Not, e))),
			Some(Err(f)) => return Err(Err::Failure(E::from_external_error(i, ErrorKind::Not, f))),
		};
		let res = f.parse(i.clone());
		match i.aux.pop_context(&res) {
			None => (),
			Some(Ok(e)) => return Err(Err::Error(E::from_external_error(i, ErrorKind::Not, e))),
			Some(Err(f)) => return Err(Err::Failure(E::from_external_error(i, ErrorKind::Not, f))),
		};
		match res {
			Ok(o) => Ok(o),
			Err(Err::Incomplete(i)) => Err(Err::Incomplete(i)),
			Err(Err::Error(e)) => Err(Err::Error(E::add_context(i, ctxt, e))),
			Err(Err::Failure(e)) => Err(Err::Failure(E::add_context(i, ctxt, e))),
		}
	}
}

impl <Aux: Copy, I> InputAux<Aux, I> {
	/// Create a new instance with a copy of the auxiliary data.
	pub fn wrap_with(&self, buf: I) -> Self {
		Self::new(self.aux, buf)
	}

	/// Create new instances, each with a copy of the auxiliary data.
	pub fn split_aux(&self, t1: I, t2: I) -> (Self, Self) {
		(Self::new(self.aux, t1), Self::new(self.aux, t2))
	}
}

impl <Aux: Default, I> From<I> for InputAux<Aux, I> {
	fn from(i: I) -> Self { InputAux::new(Default::default(), i) }
}

impl <Aux, I: PartialEq> PartialEq for InputAux<Aux, I> {
	fn eq(&self, rhs: &Self) -> bool {
		self.input == rhs.input
	}
}

impl <Aux, I: Eq> Eq for InputAux<Aux, I> { }

impl <Aux: Copy, I: Copy> Copy for InputAux<Aux, I> { }

impl <Aux, I> std::borrow::Borrow<I> for InputAux<Aux, &I> {
	fn borrow(&self) -> &I {
		self.input
	}
}

impl<Aux, I: InputLength> InputLength for InputAux<Aux, I> {
	#[inline]
	fn input_len(&self) -> usize {
		self.input.input_len()
	}
}


impl<Aux, I: Offset> Offset for InputAux<Aux, I> {
	fn offset(&self, second: &Self) -> usize {
		self.input.offset(&second.input)
	}
}


impl<Aux, I: AsBytes> AsBytes for InputAux<Aux, I> {
	#[inline(always)]
	fn as_bytes(&self) -> &[u8] {
		self.input.as_bytes()
	}
}

impl <Aux, I: InputIter> InputIter for InputAux<Aux, I> {
	type Item = <I as InputIter>::Item;
	type Iter = <I as InputIter>::Iter;
	type IterElem = <I as InputIter>::IterElem;

	fn iter_indices(&self) -> Self::Iter { self.input.iter_indices() }

	fn iter_elements(&self) -> Self::IterElem { self.input.iter_elements() }

	fn position<P: Fn(Self::Item) -> bool>(&self, p: P) -> Option<usize> {
		self.input.position(p)
	}

	fn slice_index(&self, i: usize) -> Result<usize, Needed> {
		self.input.slice_index(i)
	}
}

impl <Aux: Copy, I: InputTake> InputTake for InputAux<Aux, I> {
	fn take(&self, n: usize) -> Self {
		InputAux::new(self.aux, self.input.take(n))
	}

	fn take_split(&self, n: usize) -> (Self, Self) {
		let (t1, t2) = self.input.take_split(n);

		(InputAux::new(self.aux, t1), InputAux::new(self.aux, t2))
	}
}


impl <Aux: Copy, I: InputIter + InputTakeAtPosition> InputTakeAtPosition for InputAux<Aux, I> {
	type Item = <I as InputTakeAtPosition>::Item;

	fn split_at_position<P: Fn(Self::Item) -> bool, E: ParseError<Self>>(&self, pred: P) -> Result<(Self, Self), Err<E>> {
		let r = self.input.split_at_position::<P, (I, ErrorKind)>(pred);
		let r = r.map(|(p1, p2)| self.split_aux(p1, p2));
		let r = r.map_err(|e| e.map(|i| E::from_error_kind(self.wrap_with(i.0), i.1)));
		r
	}

	fn split_at_position1<P: Fn(Self::Item) -> bool, E: ParseError<Self>>(&self, pred: P, kind: ErrorKind) -> Result<(Self, Self), Err<E>> {
		let r = self.input.split_at_position1::<P, (I, ErrorKind)>(pred, kind);
		let r = r.map(|(p1, p2)| self.split_aux(p1, p2));
		let r = r.map_err(|e| { let ee = e.map(|i| { let o: E = E::from_error_kind(self.wrap_with(i.0), i.1); o }); ee });
		r
	}

	fn split_at_position_complete<P: Fn(Self::Item) -> bool, E: ParseError<Self>>(&self, pred: P) -> Result<(Self, Self), Err<E>> {
		let r = self.input.split_at_position_complete::<P, (I, ErrorKind)>(pred);
		let r = r.map(|(p1, p2)| self.split_aux(p1, p2));
		let r = r.map_err(|e| { let ee = e.map(|i| { let o: E = E::from_error_kind(self.wrap_with(i.0), i.1); o }); ee });
		r
	}

	fn split_at_position1_complete<P, E>(&self, pred: P, kind: ErrorKind) -> Result<(Self, Self), Err<E>>
	where
		P: Fn(Self::Item) -> bool,
		E: ParseError<Self>,
	{
		let r = self.input.split_at_position1_complete::<P, (I, ErrorKind)>(pred, kind);
		let r = r.map(|(p1, p2)| self.split_aux(p1, p2));
		let r = r.map_err(|e| { let ee = e.map(|i| { let o: E = E::from_error_kind(self.wrap_with(i.0), i.1); o }); ee });
		r
	}
}


/* Blanket impl for Compare<> makes nom::number::complete::double() fail to compile
impl <Aux, I: Compare<I>> Compare<I> for InputAux<Aux, I> {
	fn compare(&self, v: I) -> CompareResult {
		self.input.compare(v)
	}

	fn compare_no_case(&self, v: I) -> CompareResult {
		self.input.compare_no_case(v)
	}
}

*/
impl <'a, Aux, I: Compare<&'a str>> Compare<&'a str> for InputAux<Aux, I> {
	fn compare(&self, v: &'a str) -> CompareResult {
		self.input.compare(v)
	}

	fn compare_no_case(&self, v: &'a str) -> CompareResult {
		self.input.compare_no_case(v)
	}
}


impl <'a, Aux, I: Compare<&'a [u8]>> Compare<&'a [u8]> for InputAux<Aux, I> {
	fn compare(&self, v: &'a [u8]) -> CompareResult {
		self.input.compare(v)
	}

	fn compare_no_case(&self, v: &'a [u8]) -> CompareResult {
		self.input.compare_no_case(v)
	}
}


impl<Aux, T, I: FindToken<T>> FindToken<T> for InputAux<Aux, I> {
	fn find_token(&self, token: T) -> bool {
		self.input.find_token(token)
	}
}


impl<Aux, T, I: FindSubstring<T>> FindSubstring<T> for InputAux<Aux, I> {
	fn find_substring(&self, substr: T) -> Option<usize> {
		self.input.find_substring(substr)
	}
}


impl<Aux, R: FromStr, I: ParseTo<R>> ParseTo<R> for InputAux<Aux, I> {
	fn parse_to(&self) -> Option<R> {
		self.input.parse_to()
	}
}


macro_rules! aux_wrap {
		( $ty:ty ) => {
			impl <Aux: Copy, I: Slice<$ty>> Slice<$ty> for InputAux<Aux, I> {
				fn slice(&self, r: $ty) -> Self {
					self.wrap_with(self.input.slice(r))
				}
			}
		}
}

aux_wrap! {Range<usize>}
aux_wrap! {RangeTo<usize>}
aux_wrap! {RangeFrom<usize>}
aux_wrap! {RangeFull}

impl<Aux, I: std::ops::Deref> std::ops::Deref for InputAux<Aux, I> {
	type Target = <I as std::ops::Deref>::Target;

	fn deref(&self) -> &<Self as std::ops::Deref>::Target {
		self.input.deref()
	}
}

#[cfg(test)]
mod test {
	#[cfg(feature = "alloc")]
	use nom::{branch::alt, bytes::complete::tag_no_case, combinator::recognize, multi::many1};
	use nom::{
		bytes::complete::{is_a, is_not, tag, take, take_till, take_until},
		error::{self, ErrorKind},
		Err, IResult,
		Needed,
	};
	use crate::InputAux;

	#[test]
	fn tagtr_succeed() {
		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "Hello World!" };
		const TAG: &str = "Hello";
		fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			tag(TAG)(input)
		}

		match test(INPUT) {
			Ok((extra, output)) => {
				assert!(extra.input == " World!", "Parser `tag` consumed leftover input.");
				assert!(
					output.input == TAG,
					"Parser `tag` doesn't return the tag it matched on success. \
					 Expected `{}`, got `{}`.",
					TAG,
					output.input
				);
			}
			other => panic!(
				"Parser `tag` didn't succeed when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn tagtr_incomplete() {
		use nom::bytes::streaming::tag;

		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "Hello"	};
		const TAG: &str = "Hello World!";

		let res: IResult<_, _, error::Error<_>> = tag(TAG)(INPUT);
		match res {
			Err(Err::Incomplete(_)) => (),
			other => {
				panic!(
					"Parser `tag` didn't require more input when it should have. \
					 Got `{:?}`.",
					other
				);
			}
		};
	}

	#[test]
	fn tagtr_error() {
		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "Hello World!"	};
		const TAG: &str = "Random"; // TAG must be closer than INPUT.

		let res: IResult<_, _, error::Error<_>> = tag(TAG)(INPUT);
		match res {
			Err(Err::Error(_)) => (),
			other => {
				panic!(
					"Parser `tag` didn't fail when it should have. Got `{:?}`.`",
					other
				);
			}
		};
	}

	#[test]
	fn take_s_succeed() {
		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"	};
		const CONSUMED: &str = "βèƒôřèÂßÇ";
		const LEFTOVER: &str = "áƒƭèř";

		let res: IResult<_, _, error::Error<_>> = take(9_usize)(INPUT);
		match res {
			Ok((extra, output)) => {
				assert!(
					extra.input == LEFTOVER,
					"Parser `take_s` consumed leftover input. Leftover `{}`.",
					extra.input
				);
				assert!(
					output.input == CONSUMED,
					"Parser `take_s` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
					CONSUMED,
					output.input
				);
			}
			other => panic!(
				"Parser `take_s` didn't succeed when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn take_until_succeed() {
		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇ∂áƒƭèř"	};
		const FIND: &str = "ÂßÇ∂";
		const CONSUMED: &str = "βèƒôřè";
		const LEFTOVER: &str = "ÂßÇ∂áƒƭèř";

		let res: IResult<_, _, (_, ErrorKind)> = take_until(FIND)(INPUT);
		match res {
			Ok((extra, output)) => {
				assert!(
					extra.input == LEFTOVER,
					"Parser `take_until`\
					 consumed leftover input. Leftover `{}`.",
					extra.input
				);
				assert!(
					output.input == CONSUMED,
					"Parser `take_until`\
					 doens't return the string it consumed on success. Expected `{}`, got `{}`.",
					CONSUMED,
					output.input
				);
			}
			other => panic!(
				"Parser `take_until` didn't succeed when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn take_s_incomplete() {
		use nom::bytes::streaming::take;

		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇá"	};

		let res: IResult<_, _, (_, ErrorKind)> = take(13_usize)(INPUT);
		match res {
			Err(Err::Incomplete(_)) => (),
			other => panic!(
				"Parser `take` didn't require more input when it should have. \
				 Got `{:?}`.",
				other
			),
		}
	}

	fn is_alphabetic(c: char) -> bool {
		(c as u8 >= 0x41 && c as u8 <= 0x5A) || (c as u8 >= 0x61 && c as u8 <= 0x7A)
	}

	#[test]
	fn take_while() {
		use nom::bytes::streaming::take_while;

		fn f(i: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			take_while(is_alphabetic)(i)
		}
		let a = "";
		let b = "abcd";
		let c = "abcd123";
		let d = "123";

		assert_eq!(f((&a[..]).into()), Err(Err::Incomplete(Needed::new(1))));
		assert_eq!(f((&b[..]).into()), Err(Err::Incomplete(Needed::new(1))));
		assert_eq!(f((&c[..]).into()), Ok(((&d[..]).into(), (&b[..]).into())));
		assert_eq!(f((&d[..]).into()), Ok(((&d[..]).into(), (&a[..]).into())));
	}

	#[test]
	fn take_while1() {
		use nom::bytes::streaming::take_while1;

		fn f(i: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			take_while1(is_alphabetic)(i)
		}
		let a = "";
		let b = "abcd";
		let c = "abcd123";
		let d = "123";

		assert_eq!(f((&a[..]).into()), Err(Err::Incomplete(Needed::new(1))));
		assert_eq!(f((&b[..]).into()), Err(Err::Incomplete(Needed::new(1))));
		assert_eq!(f((&c[..]).into()), Ok(((&"123"[..]).into(), (&b[..]).into())));
		assert_eq!(
			f((&d[..]).into()),
			Err(Err::Error(nom::error_position!((&d[..]).into(), ErrorKind::TakeWhile1)))
		);
	}

	#[test]
	fn take_till_s_succeed() {
		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"	};
		const CONSUMED: &str = "βèƒôřèÂßÇ";
		const LEFTOVER: &str = "áƒƭèř";
		fn till_s(c: char) -> bool {
			c == 'á'
		}
		fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			take_till(till_s)(input)
		}
		match test(INPUT) {
			Ok((extra, output)) => {
				assert!(
					extra.input == LEFTOVER,
					"Parser `take_till` consumed leftover input."
				);
				assert!(
					output.input == CONSUMED,
					"Parser `take_till` doesn't return the string it consumed on success. \
					 Expected `{}`, got `{}`.",
					CONSUMED,
					output.input
				);
			}
			other => panic!(
				"Parser `take_till` didn't succeed when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn take_while_succeed_none() {
		use nom::bytes::complete::take_while;

		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"	};
		const CONSUMED: &str = "";
		const LEFTOVER: &str = "βèƒôřèÂßÇáƒƭèř";
		fn while_s(c: char) -> bool {
			c == '9'
		}
		fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			take_while(while_s)(input)
		}
		match test(INPUT) {
			Ok((extra, output)) => {
				assert!(
					extra.input == LEFTOVER,
					"Parser `take_while` consumed leftover input."
				);
				assert!(
					output.input == CONSUMED,
					"Parser `take_while` doesn't return the string it consumed on success. \
					 Expected `{}`, got `{}`.",
					CONSUMED,
					output.input
				);
			}
			other => panic!(
				"Parser `take_while` didn't succeed when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn is_not_succeed() {
		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"	};
		const AVOID: &str = "£úçƙ¥á";
		const CONSUMED: &str = "βèƒôřèÂßÇ";
		const LEFTOVER: &str = "áƒƭèř";
		fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			is_not(AVOID)(input)
		}
		match test(INPUT) {
			Ok((extra, output)) => {
				assert!(
					extra.input == LEFTOVER,
					"Parser `is_not` consumed leftover input. Leftover `{}`.",
					extra.input
				);
				assert!(
					output.input == CONSUMED,
					"Parser `is_not` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
					CONSUMED,
					output.input
				);
			}
			other => panic!(
				"Parser `is_not` didn't succeed when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn take_while_succeed_some() {
		use nom::bytes::complete::take_while;

		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"	};
		const CONSUMED: &str = "βèƒôřèÂßÇ";
		const LEFTOVER: &str = "áƒƭèř";
		fn while_s(c: char) -> bool {
			c == 'β'
				|| c == 'è'
				|| c == 'ƒ'
				|| c == 'ô'
				|| c == 'ř'
				|| c == 'è'
				|| c == 'Â'
				|| c == 'ß'
				|| c == 'Ç'
		}
		fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			take_while(while_s)(input)
		}
		match test(INPUT) {
			Ok((extra, output)) => {
				assert!(
					extra.input == LEFTOVER,
					"Parser `take_while` consumed leftover input."
				);
				assert!(
					output.input == CONSUMED,
					"Parser `take_while` doesn't return the string it consumed on success. \
					 Expected `{}`, got `{}`.",
					CONSUMED,
					output.input
				);
			}
			other => panic!(
				"Parser `take_while` didn't succeed when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn is_not_fail() {
		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"	};
		const AVOID: InputAux<(), &str> = InputAux { aux: (), input: "βúçƙ¥"	};
		fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			is_not(AVOID)(input)
		}
		match test(INPUT) {
			Err(Err::Error(_)) => (),
			other => panic!(
				"Parser `is_not` didn't fail when it should have. Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn take_while1_succeed() {
		use nom::bytes::complete::take_while1;

		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"	};
		const CONSUMED: &str = "βèƒôřèÂßÇ";
		const LEFTOVER: &str = "áƒƭèř";
		fn while1_s(c: char) -> bool {
			c == 'β'
				|| c == 'è'
				|| c == 'ƒ'
				|| c == 'ô'
				|| c == 'ř'
				|| c == 'è'
				|| c == 'Â'
				|| c == 'ß'
				|| c == 'Ç'
		}
		fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			take_while1(while1_s)(input)
		}
		match test(INPUT) {
			Ok((extra, output)) => {
				assert!(
					extra.input == LEFTOVER,
					"Parser `take_while1` consumed leftover input."
				);
				assert!(
					output.input == CONSUMED,
					"Parser `take_while1` doesn't return the string it consumed on success. \
					 Expected `{}`, got `{}`.",
					CONSUMED,
					output.input
				);
			}
			other => panic!(
				"Parser `take_while1` didn't succeed when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn take_until_incomplete() {
		use nom::bytes::streaming::take_until;

		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřè"	};
		const FIND: &str = "βèƒôřèÂßÇ";

		let res: IResult<_, _, (_, ErrorKind)> = take_until(FIND)(INPUT);
		match res {
			Err(Err::Incomplete(_)) => (),
			other => panic!(
				"Parser `take_until` didn't require more input when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn is_a_succeed() {
		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"	};
		const MATCH: &str = "βèƒôřèÂßÇ";
		const CONSUMED: &str = "βèƒôřèÂßÇ";
		const LEFTOVER: &str = "áƒƭèř";
		fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			is_a(MATCH)(input)
		}
		match test(INPUT) {
			Ok((extra, output)) => {
				assert!(
					extra.input == LEFTOVER,
					"Parser `is_a` consumed leftover input. Leftover `{}`.",
					extra.input
				);
				assert!(
					output.input == CONSUMED,
					"Parser `is_a` doens't return the string it consumed on success. Expected `{}`, got `{}`.",
					CONSUMED,
					output.input
				);
			}
			other => panic!(
				"Parser `is_a` didn't succeed when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn take_while1_fail() {
		use nom::bytes::complete::take_while1;

		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"	};
		fn while1_s(c: char) -> bool {
			c == '9'
		}
		fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			take_while1(while1_s)(input)
		}
		match test(INPUT) {
			Err(Err::Error(_)) => (),
			other => panic!(
				"Parser `take_while1` didn't fail when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn is_a_fail() {
		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř"	};
		const MATCH: &str = "Ûñℓúçƙ¥";
		fn test(input: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			is_a(MATCH)(input)
		}
		match test(INPUT) {
			Err(Err::Error(_)) => (),
			other => panic!(
				"Parser `is_a` didn't fail when it should have. Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn take_until_error() {
		use nom::bytes::streaming::take_until;

		const INPUT: InputAux<(), &str> = InputAux { aux: (), input: "βèƒôřèÂßÇáƒƭèř" };
		const FIND: &str = "Ráñδô₥";

		let res: IResult<_, _, (_, ErrorKind)> = take_until(FIND)(INPUT);
		match res {
			Err(Err::Incomplete(_)) => (),
			other => panic!(
				"Parser `take_until` didn't fail when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	#[cfg(feature = "alloc")]
	fn recognize_is_a() {
		let a = "aabbab";
		let b = "ababcd";

		fn f(i: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			recognize(many1(alt((tag("a"), tag("b")))))(i)
		}

		assert_eq!(f((&a[..]).into()), Ok(((&a[6..]).into(), (&a[..]).into())));
		assert_eq!(f((&b[..]).into()), Ok(((&b[4..]).into(), (&b[..4]).into())));
	}

	#[test]
	fn utf8_indexing() {
		fn dot(i: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			tag(".")(i)
		}

		let _ = dot("點".into());
	}

	#[cfg(feature = "alloc")]
	#[test]
	fn case_insensitive() {
		fn test(i: InputAux<(), &str>) -> IResult<InputAux<(), &str>, InputAux<(), &str>> {
			tag_no_case("ABcd")(i)
		}
		assert_eq!(test("aBCdefgh".into()), Ok(("efgh".into(), "aBCd".into())));
		assert_eq!(test("abcdefgh".into()), Ok(("efgh".into(), "abcd".into())));
		assert_eq!(test("ABCDefgh".into()), Ok(("efgh".into(), "ABCD".into())));
	}

	#[test]
	fn recurse_limit() {
		use nom::branch::alt;
		use nom::bytes::complete::tag;
		use nom::sequence::delimited;

		const DEPTH: i32 = 8;
		const INPUT: InputAux<i32, &str> = InputAux { aux: 0, input: "([([([([x])])])]) World!" };

		fn test(depth: i32, mut input: InputAux<i32, &str>) -> nom::IResult<InputAux<i32, &str>, InputAux<i32, &str>> {
			fn cp(mut i: InputAux<i32, &str>) -> nom::IResult<InputAux<i32, &str>, InputAux<i32, &str>> {
				i.aux -= 1;
				if i.aux < 0 {
					tag("never match")(i)
				} else {
					delimited(tag("("), alt((tag("x"), cp, csp)), tag(")"))(i)
				}
			}
			fn csp(mut i: InputAux<i32, &str>) -> nom::IResult<InputAux<i32, &str>, InputAux<i32, &str>> {
				i.aux -= 1;
				if i.aux < 0 {
					tag("never match")(i)
				} else {
					delimited(tag("["), alt((tag("x"), cp, csp)), tag("]"))(i)
				}
			}
			input.aux = depth;
			alt((cp, csp))(input)
		}

		match test(DEPTH, INPUT) {
			Ok((extra, output)) => {
				assert!(extra.input == " World!", "Parser `tag` consumed leftover input.");
				assert!(output.aux == 0, "Depth left over not what should be {} != 0.", output.aux);
				assert!(
					output.input == "x",
					"Parser `tag` doesn't return the tag it matched on success. \
					 Expected `{}`, got `{}`.",
					"x",
					output.input
				);
			}
			other => panic!(
				"Parser `tag` didn't succeed when it should have. \
				 Got `{:?}`.",
				other
			),
		};

		match test(DEPTH - 1, INPUT) {
			Err(Err::Error(_)) => (),
			other => panic!(
				"Parser didn't reach max depth when it should have. \
				 Got `{:?}`.",
				other
			),
		};
	}

	#[test]
	fn double_parsing() {
		assert!(1.0 < nom::number::complete::double::<_, (_, ErrorKind)>("1.2").map(|v| v.1).unwrap_or(0.0));
		assert!(1.0 < nom::number::complete::double::<_, (_, ErrorKind)>("1.2".as_bytes()).map(|v| v.1).unwrap_or(0.0));
		assert!(1.0 < nom::number::complete::double::<_, (_, ErrorKind)>(InputAux{aux: (), input: "1.2"}).map(|v| v.1).unwrap_or(0.0));
	}
}
