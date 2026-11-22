-- Prove2me | solution 1 for DeciSigma1.booleanSentence_regular_iff
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T15:23:45.884809+00:00
-- url     : https://prove2.me/submissions/fec32c9e-e588-4c2c-8b9f-b0a687fc6b78

module
public import Definitions.Def_LeanPool_DeciSigma1_Encodings
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Fresh_ElementaryBound
public import Definitions.Def_LeanPool_DeciSigma1_Holes_Tail_ClosedForm
public import Mathlib.Tactic.Ring.RingNF
public import Definitions.Def_LeanPool_DeciSigma1_Main
public import Theorems.Thm_DeciSigma1_Entailment_Logic_booleanSentence_regular_iff
public import Theorems.Thm_DeciSigma1_Full_Logic_booleanSentence_regular_iff


set_option autoImplicit true
@[expose] public section
public section
open DeciSigma1
variable {n : ℕ}
namespace DeciSigma1
theorem _root_.solution (c : Fin n → Bool) (φ : Full.Logic.BooleanSentence n) :
    φ.HoldsIn Full.Models.RegularTop c ↔ φ.HoldsIn (fun _ => True) c :=
  Full.Logic.booleanSentence_regular_iff c φ
end DeciSigma1
