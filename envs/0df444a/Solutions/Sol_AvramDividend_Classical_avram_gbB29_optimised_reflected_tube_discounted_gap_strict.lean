-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB29_optimised_reflected_tube_discounted_gap_strict
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:40:16.541883+00:00
-- url     : https://prove2.me/submissions/b84b0acc-44c5-423e-b24a-bc4201240c8c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Real
noncomputable section
theorem solution
    (y : ℝ) (hylo : (5 / 11 : ℝ) ≤ y) (hyhi : y ≤ (1 / 2 : ℝ)) :
    ((200 : ℝ) - (181 / 242 : ℝ)) *
        (1 - Real.exp (-(1 / 40000 : ℝ))) +
      Real.exp (-(1 / 40000 : ℝ)) *
        (2 * y - y ^ 2 -
          ((85 / 121 : ℝ) + (y - (5 / 11 : ℝ)))) -
        (1 / 484 : ℝ) > (1 / 484 : ℝ) := by 
  have hprod : 0 ≤ (y - (5 / 11 : ℝ)) * (1 - y - (5 / 11 : ℝ)) :=
    mul_nonneg (sub_nonneg.mpr hylo) (by linarith)
  have hdelta : 0 ≤ 2 * y - y ^ 2 -
      ((85 / 121 : ℝ) + (y - (5 / 11 : ℝ))) := by
    nlinarith [hprod]
  have hePos : 0 ≤ Real.exp (-(1 / 40000 : ℝ)) :=
    le_of_lt (Real.exp_pos _)
  have heBound : Real.exp (-(1 / 40000 : ℝ)) ≤
      (40000 / 40001 : ℝ) := by
    have hx : (1 : ℝ) / Real.exp (1 / 40000 : ℝ) ≤
        40000 / 40001 := by
      apply (div_le_iff₀ (Real.exp_pos _)).2
      nlinarith [Real.add_one_le_exp (1 / 40000 : ℝ)]
    simpa only [Real.exp_neg, one_div] using hx
  have hTerm : 0 ≤ Real.exp (-(1 / 40000 : ℝ)) *
      (2 * y - y ^ 2 -
        ((85 / 121 : ℝ) + (y - (5 / 11 : ℝ)))) :=
    mul_nonneg hePos hdelta
  nlinarith [hTerm]
