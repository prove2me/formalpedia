-- Prove2me | solution 1 for FixedPointAA.Main.reflections_matrix_form
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T15:06:15.829806+00:00
-- url     : https://prove2.me/submissions/71fc9e34-8cbb-4a2e-b3f4-451dcccf20f1

import Mathlib
import Definitions.Def_FixedPointAA_Main_Setting
set_option autoImplicit false
open FixedPointAA.Main
open scoped Matrix

theorem solution (lam : ℝ) (h0 : 0 ≤ lam) (h1 : lam ≤ 1) (α β : ℝ) :
    Ss (sVec lam) α =
      !![1 - (1 - Complex.exp (-(α : ℂ) * Complex.I)) * ((1 - lam : ℝ) : ℂ),
          -(1 - Complex.exp (-(α : ℂ) * Complex.I)) * ((Real.sqrt (lam * (1 - lam)) : ℝ) : ℂ);
          -(1 - Complex.exp (-(α : ℂ) * Complex.I)) * ((Real.sqrt (lam * (1 - lam)) : ℝ) : ℂ),
          1 - (1 - Complex.exp (-(α : ℂ) * Complex.I)) * (lam : ℂ)] ∧
    St tVec β = !![1, 0; 0, Complex.exp ((β : ℂ) * Complex.I)] := by
  have hsq1 : ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt (1 - lam) : ℝ) : ℂ) = ((1 - lam : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by linarith)]
  have hsq2 : ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) = (lam : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt h0]
  have hsq3 : ((Real.sqrt (1 - lam) : ℝ) : ℂ) * ((Real.sqrt lam : ℝ) : ℂ) = ((Real.sqrt (lam * (1 - lam)) : ℝ) : ℂ) := by
    rw [← Complex.ofReal_mul, Real.sqrt_mul h0, mul_comm]
  have hsq4 : ((Real.sqrt lam : ℝ) : ℂ) * ((Real.sqrt (1 - lam) : ℝ) : ℂ) = ((Real.sqrt (lam * (1 - lam)) : ℝ) : ℂ) := by
    rw [mul_comm]; exact hsq3
  constructor
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Ss, sVec, Matrix.vecMulVec, hsq1, hsq2, hsq3, hsq4] <;> ring
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [St, tVec, Matrix.vecMulVec]
