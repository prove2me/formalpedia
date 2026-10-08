-- Prove2me | solution 3 for AvramDividend.Classical.finite_small_negative_jump_square_moment
-- status  : ACCEPTED   (prove)
-- author  : @savarin
-- created : 2026-10-06T16:45:47.894999+00:00
-- url     : https://prove2.me/submissions/986df07c-f9b5-4905-a699-96bab83005fe

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    (ν : Measure ℝ)
    (hν : (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν) < ⊤) :
    (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal (y ^ 2) ∂ν) < ⊤ := by
  refine lt_of_le_of_lt ?_ hν
  calc (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal (y ^ 2) ∂ν)
      ≤ ∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν := by
        apply setLIntegral_mono' measurableSet_Ioo
        intro y hy
        apply ENNReal.ofReal_le_ofReal
        have h1 : y ^ 2 ≤ 1 := by
          obtain ⟨a, b⟩ := hy
          nlinarith
        exact le_of_eq (min_eq_right h1).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (min 1 (y ^ 2)) ∂ν := setLIntegral_le_lintegral _ _
