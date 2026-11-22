-- Prove2me | solution 1 for DeciSigma1.decideBooleanSentenceTopFree_correct
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:28:19.150126+00:00
-- url     : https://prove2.me/submissions/c957efd4-cea0-4995-a7e8-68403412a099

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
theorem _root_.solution (C : Entailment.Logic.TreeClass)
    (φ : Entailment.Logic.BooleanSentence n) :
    @decide _ (decideBooleanSentenceTopFree C φ) = true ↔ φ.HoldsIn C.Contains :=
  @decide_eq_true_iff _ (decideBooleanSentenceTopFree C φ)
end DeciSigma1
