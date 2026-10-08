-- Prove2me | solution 1 for AvramDividend.Classical.negative_exponential_quotient_bounds
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T06:12:38.403007+00:00
-- url     : https://prove2.me/submissions/118438a2-5ba4-44db-a013-fbbaf2bf0ab9

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    (θ y : ℝ) (hθ : 0 < θ) (hy : y < 0) :
    0 ≤ (1 - Real.exp (θ * y)) / θ ∧
      (1 - Real.exp (θ * y)) / θ ≤ |y| := by
  have hz : θ * y ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hθ.le hy.le
  have hle : Real.exp (θ * y) ≤ 1 :=
    Real.exp_le_one_iff.mpr hz
  have hge : 1 + θ * y ≤ Real.exp (θ * y) := by
    simpa only [add_comm] using (Real.add_one_le_exp (θ * y))
  constructor
  · exact div_nonneg (sub_nonneg.mpr hle) hθ.le
  · rw [abs_of_neg hy]
    apply (div_le_iff₀ hθ).2
    nlinarith
