-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB29_optimised_quadratic_and_caplinear_generator_signs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T12:41:53.938704+00:00
-- url     : https://prove2.me/submissions/fea8b304-5aba-4ab9-9c03-48b5f3036b6e

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

noncomputable section
theorem solution
    (y : ℝ) (hy0 : 0 < y) (hyC : y < (1 / 2 : ℝ)) :
    (y ^ 2 / 100 - (201 / 50 : ℝ) * y) < 0 ∧
      0 < 2 - (1 / 100 : ℝ) * (y + (30 / 121 : ℝ)) ∧
      (1 : ℝ) ≤ 2 - 2 * y := by 
  have hprod : 0 ≤ y * ((1 / 2 : ℝ) - y) :=
    mul_nonneg (le_of_lt hy0) (sub_nonneg.mpr (le_of_lt hyC))
  constructor
  · nlinarith [hprod]
  · constructor
    · nlinarith [hyC]
    · linarith
