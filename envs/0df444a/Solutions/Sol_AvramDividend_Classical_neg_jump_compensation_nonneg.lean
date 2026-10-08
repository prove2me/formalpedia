-- Prove2me | solution 1 for AvramDividend.Classical.neg_jump_compensation_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T13:05:37.921704+00:00
-- url     : https://prove2.me/submissions/21fa5ae7-bd2b-471b-b8ed-258f3e062cde

import Mathlib

theorem solution (θ y : ℝ) (hθ : 0 < θ) :
    0 ≤ (Real.exp (θ * y) - 1) / θ - y := by
  have he : θ * y + 1 ≤ Real.exp (θ * y) :=
    Real.add_one_le_exp (θ * y)
  have hd : y ≤ (Real.exp (θ * y) - 1) / θ := by
    apply (le_div_iff₀ hθ).2
    nlinarith
  exact sub_nonneg.mpr hd
