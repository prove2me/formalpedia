-- Prove2me | solution 1 for CogCons.cwo_iInter_of_deductive
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:21:28.730985+00:00
-- url     : https://prove2.me/submissions/0f5204f6-3734-4b9a-a884-a63e1f2e4d9c

import Definitions.Def_CogCons_consequence_space
import Mathlib.Tactic
open CogCons CogCons.CognitiveConsequenceSpace

theorem solution {C : Type*} (S : CognitiveConsequenceSpace C) {ι : Type*}
    (A : ι → Set C) (hA : ∀ i, S.IsCWO (A i))
    (hU : S.IsDeductive (⋃ i, (A i)ᶜ)) :
    S.IsCWO (⋂ i, A i) := by
  change S.Cn (⋂ i,A i)ᶜ=(⋂ i,A i)ᶜ
  rw [Set.compl_iInter]
  exact hU
