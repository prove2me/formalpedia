-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixLengthEnvelope_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:05.023891+00:00
-- url     : https://prove2.me/submissions/6f11f37b-1870-4afc-b5d7-93d6b75cc965

module
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_Rays
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedFactors

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1 DeciSigma1.Holes DeciSigma1.Holes.Tail
open DeciSigma1.Words
variable {α S : Type} {k : ℕ}
namespace DeciSigma1.Holes.Tail
theorem _root_.solution (m N S : ℕ) (Ss : List ℕ) (b : ℕ) :
    suffixLengthEnvelope m N (S :: Ss) b =
      suffixLengthEnvelope m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
        suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b)) := rfl
end DeciSigma1.Holes.Tail
