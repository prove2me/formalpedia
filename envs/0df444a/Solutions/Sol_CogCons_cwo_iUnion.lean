-- Prove2me | solution 1 for CogCons.cwo_iUnion
-- status  : ACCEPTED   (prove)
-- author  : @ryanshin
-- created : 2026-09-30T17:20:55.510844+00:00
-- url     : https://prove2.me/submissions/bf8ca4c7-01e2-4f15-98be-e9010825b5e8

import Definitions.Def_CogCons_consequence_space
import Mathlib.Tactic
open CogCons CogCons.CognitiveConsequenceSpace

theorem solution {C : Type*} (S : CognitiveConsequenceSpace C) {ι : Type*}
    (A : ι → Set C) (hA : ∀ i, S.IsCWO (A i)) :
    S.IsCWO (⋃ i, A i) := by
  change S.Cn (⋃ i,A i)ᶜ=(⋃ i,A i)ᶜ
  apply Set.Subset.antisymm _ (S.subset_Cn _)
  intro x hx
  change x∉⋃ i,A i
  intro hxA
  obtain ⟨i,hi⟩:=Set.mem_iUnion.mp hxA
  have hs : (⋃ i,A i)ᶜ ⊆ (A i)ᶜ := by
    intro y hy hyi
    exact hy (Set.mem_iUnion.mpr ⟨i,hyi⟩)
  have hh:=S.Cn_mono _ _ hs hx
  have hAi : S.Cn (A i)ᶜ=(A i)ᶜ := hA i
  rw [hAi] at hh
  exact hh hi
