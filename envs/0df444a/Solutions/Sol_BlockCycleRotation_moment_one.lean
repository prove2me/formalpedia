-- Prove2me | solution 1 for BlockCycleRotation.moment_one
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:05:01.549511+00:00
-- url     : https://prove2.me/submissions/8e14f7bc-826e-4006-b113-ea9f90cafbd3

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Definitions.Def_BlockCycleRotation_Theorem10
import Mathlib

open Finset Real Filter Topology MeasureTheory BoxIntegral
open scoped ENNReal

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

/-- Integration against the uniform measure is `2·∫₀^{1/2}`. -/
theorem integral_unifHalf (g : ℝ → ℝ) :
    ∫ x, g x ∂unifHalf = 2 * ∫ x in (0 : ℝ)..(1 / 2), g x := by
  rw [unifHalf, MeasureTheory.integral_smul_measure,
    intervalIntegral.integral_of_le (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  simp

end BlockCycleRotation

open BlockCycleRotation in
/-- The first moment is the constant of Theorem 10. -/
theorem solution : ∫ x, fCost x ^ 1 ∂unifHalf = 2 * ∫ x in (0 : ℝ)..(1 / 2), fCost x:= by
  rw [integral_unifHalf]
  simp
