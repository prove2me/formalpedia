-- Prove2me | solution 1 for DeciSigma1.Holes.Tail.suffixLengthEnvelope_nil
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T12:44:23.425584+00:00
-- url     : https://prove2.me/submissions/49319b7d-a9fa-402d-9b49-fca46b945463

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
theorem _root_.solution (m N b : ℕ) : suffixLengthEnvelope m N [] b = b := rfl
end DeciSigma1.Holes.Tail
