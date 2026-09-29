-- Prove2me | solution 1 for CalibratedCE.Convergence.Mp_subset_Mb
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-09-27T22:16:19.045402+00:00
-- url     : https://prove2.me/submissions/18701bc4-df3b-4d72-8529-1c03f9cfed54

import Mathlib
import Definitions.Def_CalibratedCE_Convergence_Game
import Definitions.Def_CalibratedCE_Convergence_BestReply

open CalibratedCE.Convergence

theorem solution {m n : ℕ} (u₁ : Fin m → Fin n → ℝ) (R₁ : (Fin n → ℝ) → Fin m)
    (hR₁ : IsBestReply₁ u₁ R₁) (a : Fin m) : Mp R₁ a ⊆ Mb u₁ a := by
  intro p hp
  obtain ⟨hdist, hRa⟩ := hp
  refine ⟨hdist, ?_⟩
  intro a'
  have h := hR₁ p hdist a'
  rw [hRa] at h
  exact h
