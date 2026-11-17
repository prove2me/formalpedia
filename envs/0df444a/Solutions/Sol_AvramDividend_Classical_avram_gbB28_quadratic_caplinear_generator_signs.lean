-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB28_quadratic_caplinear_generator_signs
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T11:26:12.097612+00:00
-- url     : https://prove2.me/submissions/7978718c-ef26-4d49-837f-a55977010de2

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
noncomputable section
theorem solution
    (y : ℝ) (hy0 : 0 < y) (hyC : y < (2 / 5 : ℝ)) :
    y ^ 2 - 4 * y - 2 < 0 ∧
      0 < 1 - (y + (4 / 25 : ℝ)) := by 
  have hmul : 0 ≤ y * ((2 / 5 : ℝ) - y) :=
    mul_nonneg (le_of_lt hy0) (sub_nonneg.mpr (le_of_lt hyC))
  constructor
  · nlinarith [hmul]
  · linarith
