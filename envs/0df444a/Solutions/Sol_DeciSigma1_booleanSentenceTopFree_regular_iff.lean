-- Prove2me | solution 1 for DeciSigma1.booleanSentenceTopFree_regular_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:26:30.714211+00:00
-- url     : https://prove2.me/submissions/b5324adb-0a38-42fc-8d19-4caa043ba3a7

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Theorems.Thm_DeciSigma1_booleanSentence_regular_iff
public import Theorems.Thm_DeciSigma1_Entailment_Logic_booleanSentence_regular_iff
public import Theorems.Thm_DeciSigma1_Full_Logic_booleanSentence_regular_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {n : ℕ}
namespace DeciSigma1
theorem _root_.solution (φ : Entailment.Logic.BooleanSentence n) :
    φ.HoldsIn Semantics.IsRegularTree ↔ φ.HoldsIn (fun _ => True) :=
  Entailment.Logic.booleanSentence_regular_iff φ
end DeciSigma1
