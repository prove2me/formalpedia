-- Prove2me | solution 2 for AvramDividend.Classical.levy_compensated_exponential_kernel_bounds
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T20:07:12.938247+00:00
-- url     : https://prove2.me/submissions/3afe898a-699c-47bd-98ad-26133b88c375

import Mathlib

theorem solution
    (θ t : ℝ) (hθ : 0 ≤ θ) (ht : 0 ≤ t) :
    0 ≤ 1 - Real.exp (-θ * t) ∧
      1 - Real.exp (-θ * t) ≤ θ * t := by
  have harg : -θ * t ≤ 0 := mul_nonpos_of_nonpos_of_nonneg (neg_nonpos.mpr hθ) ht
  constructor
  · exact sub_nonneg.mpr (Real.exp_le_one_iff.mpr harg)
  · have hexp : 1 - θ * t ≤ Real.exp (-θ * t) := by
      simpa [neg_mul] using Real.one_sub_le_exp_neg (θ * t)
    linarith
