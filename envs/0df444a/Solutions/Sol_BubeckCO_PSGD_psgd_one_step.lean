-- Prove2me | solution 1 for BubeckCO.PSGD.psgd_one_step
-- status  : ACCEPTED   (prove)
-- author  : @kmehltretter82
-- created : 2026-11-01T22:28:29.832756+00:00
-- url     : https://prove2.me/submissions/d63e33fb-a12a-4688-bcde-82c844c76067

import Mathlib
import Definitions.Def_BubeckCO_PSGD_IsSubgradient
set_option autoImplicit false

open BubeckCO.PSGD

theorem solution {n : ℕ} (X : Set (EuclideanSpace ℝ (Fin n)))
    (f : EuclideanSpace ℝ (Fin n) → ℝ) (η : ℝ) (hη : 0 < η)
    (xs gs ys xstar : EuclideanSpace ℝ (Fin n))
    (hgs : IsSubgradient X f xs gs) (hys : ys = xs - η • gs) (hxstar : xstar ∈ X) :
    f xs - f xstar ≤ inner ℝ gs (xs - xstar) ∧
      inner ℝ gs (xs - xstar) = 1 / η * inner ℝ (xs - ys) (xs - xstar) ∧
      1 / η * inner ℝ (xs - ys) (xs - xstar) =
        1 / (2 * η) * (‖xs - xstar‖ ^ 2 + ‖xs - ys‖ ^ 2 - ‖ys - xstar‖ ^ 2) ∧
      1 / (2 * η) * (‖xs - xstar‖ ^ 2 + ‖xs - ys‖ ^ 2 - ‖ys - xstar‖ ^ 2) =
        1 / (2 * η) * (‖xs - xstar‖ ^ 2 - ‖ys - xstar‖ ^ 2) + η / 2 * ‖gs‖ ^ 2 := by
  have hη0 : η ≠ 0 := hη.ne'
  have hxs_ys : xs - ys = η • gs := by rw [hys, sub_sub_cancel]
  refine ⟨hgs.2 xstar hxstar, ?_, ?_, ?_⟩
  · rw [hxs_ys, real_inner_smul_left]
    field_simp
  · have h_sub : (xs - ys) - (xs - xstar) = xstar - ys := by abel
    have h_norm : ‖ys - xstar‖ ^ 2 =
        ‖xs - ys‖ ^ 2 - 2 * inner ℝ (xs - ys) (xs - xstar) + ‖xs - xstar‖ ^ 2 := by
      rw [← norm_neg (ys - xstar), neg_sub, ← h_sub, norm_sub_sq_real]
    rw [h_norm]
    field_simp
    ring
  · have h_norm_gs : ‖xs - ys‖ = η * ‖gs‖ := by
      rw [hxs_ys, norm_smul, Real.norm_of_nonneg hη.le]
    rw [h_norm_gs]
    field_simp
    ring
