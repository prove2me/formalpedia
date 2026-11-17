-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB30_sigma1_halfband_discounted_strict_gap
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T13:35:35.360793+00:00
-- url     : https://prove2.me/submissions/1501e7be-00fe-4daa-8835-4929432a5d77

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section
theorem solution
    (y : ℝ) (hylo : (5 / 44 : ℝ) ≤ y)
    (hyhi : y ≤ (1 / 8 : ℝ)) :
    ((193419 / 968 : ℝ) *
        (1 - Real.exp (-(1 / 40000 : ℝ))) +
      Real.exp (-(1 / 40000 : ℝ)) *
        (y - 4 * y ^ 2 - (15 / 242 : ℝ)) -
        (1 / 1936 : ℝ)) > (1 / 1936 : ℝ) := by 
  have hprod : 0 ≤ (y - (5 / 44 : ℝ)) *
      ((3 / 22 : ℝ) - y) :=
    mul_nonneg (sub_nonneg.mpr hylo) (by linarith)
  have hdelta : 0 ≤ y - 4 * y ^ 2 - (15 / 242 : ℝ) := by
    nlinarith [hprod]
  have hExpPos : 0 ≤ Real.exp (-(1 / 40000 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hExpBound : Real.exp (-(1 / 40000 : ℝ)) ≤
      (40000 / 40001 : ℝ) := by
    have h : (1 : ℝ) / Real.exp (1 / 40000 : ℝ) ≤
        40000 / 40001 := by
      apply (div_le_iff₀ (Real.exp_pos _)).2
      nlinarith [Real.add_one_le_exp (1 / 40000 : ℝ)]
    simpa only [Real.exp_neg, one_div] using h
  have hTerm : 0 ≤ Real.exp (-(1 / 40000 : ℝ)) *
      (y - 4 * y ^ 2 - (15 / 242 : ℝ)) :=
    mul_nonneg hExpPos hdelta
  nlinarith [hTerm]
