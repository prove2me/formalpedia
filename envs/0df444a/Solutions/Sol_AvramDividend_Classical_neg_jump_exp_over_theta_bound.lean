-- Prove2me | solution 1 for AvramDividend.Classical.neg_jump_exp_over_theta_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T12:10:54.204979+00:00
-- url     : https://prove2.me/submissions/ea4b5a4c-b54b-44a6-a1bf-879e8401c922

import Mathlib

theorem solution
    (θ y : ℝ) (hθ : 0 < θ) (hy : y ≤ 0) :
    0 ≤ (1 - Real.exp (θ * y)) / θ ∧
      (1 - Real.exp (θ * y)) / θ ≤ -y := by
  have hty : θ * y ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hθ.le hy
  have hexp : Real.exp (θ * y) ≤ 1 := by
    have h := (Real.exp_le_exp).2 hty
    simpa only [Real.exp_zero] using h
  have htan := Real.add_one_le_exp (θ * y)
  constructor
  · exact div_nonneg (sub_nonneg.mpr hexp) hθ.le
  · apply (div_le_iff₀ hθ).2
    nlinarith
