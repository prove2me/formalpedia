-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB28_reflected_tube_terminal_gap_strict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:30:58.577196+00:00
-- url     : https://prove2.me/submissions/9a7f8199-72b0-4035-978d-1f133767b660

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section
theorem solution
    (y : ℝ) (hylo : (19 / 50 : ℝ) ≤ y) (hyhi : y ≤ (2 / 5 : ℝ)) :
    (11 / 25 : ℝ) * (1 - Real.exp (-(2 / 5 : ℝ))) +
      Real.exp (-(2 / 5 : ℝ)) * (y - y ^ 2 - (4 / 25 : ℝ)) -
        (2 / 25 : ℝ) > (2 / 25 : ℝ) := by 
  have hprod : 0 ≤ (y - (19 / 50 : ℝ)) * (1 - y - (19 / 50 : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hylo) (by linarith)
  have hdelta : (189 / 2500 : ℝ) ≤ y - y ^ 2 - (4 / 25 : ℝ) := by
    nlinarith [hprod]
  have hExpPos : 0 ≤ Real.exp (-(2 / 5 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have hExpBound : Real.exp (-(2 / 5 : ℝ)) ≤ (5 / 7 : ℝ) := by
    have hx : (1 : ℝ) / Real.exp (2 / 5 : ℝ) ≤ 5 / 7 := by
      apply (div_le_iff₀ (Real.exp_pos _)).2
      nlinarith [Real.add_one_le_exp (2 / 5 : ℝ)]
    simpa only [Real.exp_neg, one_div] using hx
  have hMul : 0 ≤
      Real.exp (-(2 / 5 : ℝ)) *
        ((y - y ^ 2 - (4 / 25 : ℝ)) - (189 / 2500 : ℝ)) :=
    mul_nonneg hExpPos (sub_nonneg.mpr hdelta)
  nlinarith [hMul]
