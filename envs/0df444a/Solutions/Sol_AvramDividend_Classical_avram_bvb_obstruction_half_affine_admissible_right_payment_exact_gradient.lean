-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb_obstruction_half_affine_admissible_right_payment_exact_gradient
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T07:44:09.859564+00:00
-- url     : https://prove2.me/submissions/9e80fb0a-63cc-4c9d-8de3-f5148d028aeb

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution (r Δ : ℝ) (hΔ : 0 ≤ Δ) (hBound : Δ ≤ r) :
    Δ ≤
      (if r < 0 then 0 else 1 / 2 + r) -
      (if r - Δ < 0 then 0 else 1 / 2 + (r - Δ)) := by
  have hr : ¬ r < 0 := not_lt.mpr (le_trans hΔ hBound)
  have hpost : ¬ r - Δ < 0 :=
    not_lt.mpr (sub_nonneg.mpr hBound)
  simp only [hr, hpost, if_false]
  linarith
