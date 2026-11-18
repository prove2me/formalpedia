-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB36_short_horizon_sigma1_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T15:32:32.270359+00:00
-- url     : https://prove2.me/submissions/b556c98b-a7e7-4b97-adfa-831e966016a9

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gbB34_sigma1_upper_band_positive_drift
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical
noncomputable section
/-- Shorter stopping time still gives a strict positive cap-gap excess. -/
theorem solution (y : ℝ)
  (hylo : (5 / 44 : ℝ) ≤ y) (hyhi : y ≤ (1 / 8 : ℝ)) :
  ((193419 / 968 : ℝ) * (1 - Real.exp (-(1 / 100000 : ℝ))) +
    Real.exp (-(1 / 100000 : ℝ)) *
      (y - 4 * y ^ 2 - (15 / 242 : ℝ)) -
    (1 / 1936 : ℝ)) > (1 / 1936 : ℝ) := by
  have hNonneg :=
    (avram_gbB34_sigma1_upper_band_positive_drift y hylo hyhi).2.1
  have hExpPos : 0 ≤ Real.exp (-(1 / 100000 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hExpBound : Real.exp (-(1 / 100000 : ℝ)) ≤
      (100000 / 100001 : ℝ) := by
    have h : (1 : ℝ) / Real.exp (1 / 100000 : ℝ) ≤
        100000 / 100001 := by
      apply (div_le_iff₀ (Real.exp_pos _)).2
      nlinarith [Real.add_one_le_exp (1 / 100000 : ℝ)]
    simpa only [Real.exp_neg, one_div] using h
  have hTerm : 0 ≤ Real.exp (-(1 / 100000 : ℝ)) *
      (y - 4 * y ^ 2 - 15 / 242) :=
    mul_nonneg hExpPos hNonneg
  nlinarith [hTerm]
