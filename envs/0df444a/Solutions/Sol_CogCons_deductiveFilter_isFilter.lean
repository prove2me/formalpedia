-- Prove2me | solution 1 for CogCons.deductiveFilter_isFilter
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:11:33.455513+00:00
-- url     : https://prove2.me/submissions/a091753a-1e09-4ba2-9d39-15dc63b2fda9

import Definitions.Def_CogCons_consequence_space

open CogCons CogCons.CognitiveConsequenceSpace

theorem solution {C : Type*} (S : CognitiveConsequenceSpace C)
    (Cd : Set C) (hCd : S.IsDeductive Cd) (hCd_ne : Cd ≠ Set.univ) (f : C) (hf : f ∈ Cd) :
    Cd ∈ S.deductiveFilter Cd f ∧
    (∀ A B : Set C, A ∈ S.deductiveFilter Cd f → A ⊆ B → B ⊆ Cd →
      B ∈ S.deductiveFilter Cd f) ∧
    (∀ A B : Set C, A ∈ S.deductiveFilter Cd f → B ∈ S.deductiveFilter Cd f →
      A ∩ B ∈ S.deductiveFilter Cd f) := by
  refine ⟨⟨Set.Subset.rfl, hf, Cd, Set.Subset.rfl, hCd⟩, ?_, ?_⟩
  · rintro A B ⟨_, hfA, D, hDA, hD⟩ hAB hBCd
    exact ⟨hBCd, hAB hfA, D, hDA.trans hAB, hD⟩
  · rintro A B ⟨hA, hfA, D, hDA, hD⟩ ⟨hB, hfB, E, hEB, hE⟩
    refine ⟨fun x hx => hA hx.1, ⟨hfA, hfB⟩, D ∩ E, ?_, ?_⟩
    · intro x hx
      exact ⟨hDA hx.1, hEB hx.2⟩
    · apply Set.Subset.antisymm
      · intro x hx
        have hd := S.Cn_mono (D ∩ E) D Set.inter_subset_left hx
        have he := S.Cn_mono (D ∩ E) E Set.inter_subset_right hx
        rw [hD] at hd
        rw [hE] at he
        exact ⟨hd, he⟩
      · exact S.subset_Cn _
