-- Prove2me | solution 1 for AvramDividend.Classical.avram_gen15_affine_singular_hjb_deficit_strictly_negative
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T14:57:59.552406+00:00
-- url     : https://prove2.me/submissions/e595516c-5cbb-4092-a56d-9c57ecf85b7c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section

/-- The source affine HJB deficit is strictly negative at every positive reserve. -/
theorem solution (x : ℝ) (hx : 0 < x) :
    3 - 4 * x ^ (1 / 2 : ℝ) - 2 * x ^ (-(1 / 2 : ℝ)) < 0 := by
  have hs : 0 < x ^ (1 / 2 : ℝ) := Real.rpow_pos_of_pos hx _
  have hprod :
      x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) = 1 := by
    calc
      x ^ (1 / 2 : ℝ) * x ^ (-(1 / 2 : ℝ)) =
          x ^ ((1 / 2 : ℝ) + (-(1 / 2 : ℝ))) :=
        (Real.rpow_add hx (1 / 2 : ℝ) (-(1 / 2 : ℝ))).symm
      _ = 1 := by norm_num
  by_contra hneg
  have hnonneg : 0 ≤
      3 - 4 * x ^ (1 / 2 : ℝ) - 2 * x ^ (-(1 / 2 : ℝ)) :=
    le_of_not_gt hneg
  have hproduct := mul_nonneg (le_of_lt hs) hnonneg
  nlinarith [sq_nonneg (2 * x ^ (1 / 2 : ℝ) - 1)]
