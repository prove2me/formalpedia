-- Prove2me | solution 1 for CogCons.coincide_of_convergesTo_of_convergesTo
-- status  : ACCEPTED   (prove)
-- author  : @BrunoDCDO
-- created : 2026-09-30T22:11:02.946455+00:00
-- url     : https://prove2.me/submissions/c583f010-2de2-4d45-8972-a25c274657f3

import Definitions.Def_CogCons_similarity_distance

open CogCons CogCons.CognitiveSimilarityDistance

theorem solution {C : Type*} (D : CognitiveSimilarityDistance C)
    (s : ℕ → C) (x₁ x₂ : C) (h₁ : D.ConvergesTo s x₁) (h₂ : D.ConvergesTo s x₂) :
    D.coincide x₁ x₂ := by
  apply (D.Cog_eq_zero_iff x₁ x₂).mp
  by_contra hn
  have hb := D.Cog_mem_Icc x₁ x₂
  have hp : 0 < D.Cog x₁ x₂ := lt_of_le_of_ne hb.1 (Ne.symm hn)
  have he : D.Cog x₁ x₂ / 3 ∈ Set.Ioo (0 : ℝ) 1 := by constructor <;> linarith [hb.2]
  obtain ⟨m, hm⟩ := h₁ _ he
  obtain ⟨n, hn⟩ := h₂ _ he
  have hfirst := hm (max m n) (le_max_left _ _)
  have hsecond := hn (max m n) (le_max_right _ _)
  have ht := D.Cog_triangle x₁ (s (max m n)) x₂
  rw [D.Cog_symm (s (max m n)) x₂] at ht
  linarith
