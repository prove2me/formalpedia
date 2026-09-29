-- Prove2me | solution 1 for FamousTheorems.riesz_lemma_normed_space
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T02:08:11.840424+00:00
-- url     : https://prove2.me/submissions/dfb99fe8-6df8-480a-a8ff-c55f5c635949

import Mathlib

theorem solution {𝕜 E : Type*} [NormedField 𝕜] [NormedAddCommGroup E] [NormedSpace 𝕜 E] {F : Subspace 𝕜 E}
    (hFc : IsClosed (F : Set E)) (hF : ∃ x : E, x ∉ F) {r : ℝ} (hr : r < 1) :
    ∃ x₀ ∉ F, ∀ y ∈ F, r * ‖x₀‖ ≤ ‖x₀ - y‖ :=
  riesz_lemma hFc hF hr
