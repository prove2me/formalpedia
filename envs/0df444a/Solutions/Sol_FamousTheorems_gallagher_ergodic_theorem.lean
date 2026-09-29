-- Prove2me | solution 1 for FamousTheorems.gallagher_ergodic_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:14:39.709985+00:00
-- url     : https://prove2.me/submissions/473aa293-9ab0-40ad-8e46-1bcec1ea3fa9

import Mathlib

theorem solution {T : ℝ} [Fact (0 < T)] (δ : ℕ → ℝ) (hδ : Filter.Tendsto δ Filter.atTop (nhds 0)) :
    (∀ᵐ (x : AddCircle T), x ∉ addWellApproximable (AddCircle T) δ) ∨
      ∀ᵐ (x : AddCircle T), x ∈ addWellApproximable (AddCircle T) δ :=
  AddCircle.addWellApproximable_ae_empty_or_univ δ hδ
