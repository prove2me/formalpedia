-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixLengthBound_cons
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:52:04.563517+00:00
-- url     : https://prove2.me/submissions/7dee500e-dd69-4ef2-af06-2a1ff68441b5

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
    suffixLengthBound m N (S :: Ss) b =
      2 * suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b) +
        suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b +
          suffixLengthBound m N Ss ((fun b => b + suffixLengthBound m N Ss b)^[S] b)) + 2 := rfl
end DeciSigma1.Holes.Tail
