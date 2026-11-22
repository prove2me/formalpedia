-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixLengthBound_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:44:15.231006+00:00
-- url     : https://prove2.me/submissions/078e9595-9139-4e7c-93de-558c1ce51056

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
theorem _root_.solution (m N b : ℕ) :
    suffixLengthBound m N [] b = factorLengthBound m N b + 1 := rfl
end DeciSigma1.Holes.Tail
