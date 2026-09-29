-- Prove2me | solution 1 for BlockCycleRotation.moment_fCost
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T12:04:42.258552+00:00
-- url     : https://prove2.me/submissions/da3a1b6a-7df6-44fa-a517-2645268a75bc

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
/-- **The corollary.**  For `X` uniform on `[0,1/2]`, the `j`-th moment of
`f(X)` is `(∫₀^{1/2} f^j)/(1/2)`. -/
theorem solution (j : ℕ) :
    ∫ x, fCost x ^ j ∂unifHalf = (∫ x in (0 : ℝ)..(1 / 2), fCost x ^ j) / (1 / 2):= by
  rw [integral_unifHalf]
  ring
