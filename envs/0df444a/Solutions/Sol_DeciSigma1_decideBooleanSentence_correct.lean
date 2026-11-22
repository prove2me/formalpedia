-- Prove2me | solution 1 for DeciSigma1.decideBooleanSentence_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:28:14.839912+00:00
-- url     : https://prove2.me/submissions/4f40684a-1c8e-4942-be19-4331e4efdf4b

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main

set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {n : ℕ}
namespace DeciSigma1
theorem _root_.solution (c : Fin n → Bool) (C : Full.Logic.TreeClass)
    (φ : Full.Logic.BooleanSentence n) :
    @decide _ (decideBooleanSentence c C φ) = true ↔ φ.HoldsIn C.Contains c :=
  @decide_eq_true_iff _ (decideBooleanSentence c C φ)
end DeciSigma1
