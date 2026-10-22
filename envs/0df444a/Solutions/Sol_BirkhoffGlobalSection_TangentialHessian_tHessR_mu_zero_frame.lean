-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.tHessR_mu_zero_frame
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T17:35:18.060317+00:00
-- url     : https://prove2.me/submissions/59e4cfa5-3c49-499c-9e7c-adde3e71504b

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.NormNum

set_option maxRecDepth 20000 in
open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian in
theorem solution (c r : ℝ) (s : Phase) :
    tHessR 0 c r s = !![kGradR 0 c r s 2, kGradR 0 c r s 3, -kGradR 0 c r s 0, -kGradR 0 c r s 1; kGradR 0 c r s 1, -kGradR 0 c r s 0, -kGradR 0 c r s 3, kGradR 0 c r s 2; -kGradR 0 c r s 3, kGradR 0 c r s 2, -kGradR 0 c r s 1, kGradR 0 c r s 0] * !![kHessR 0 c r s 0 0, kHessR 0 c r s 0 1, kHessR 0 c r s 0 2, kHessR 0 c r s 0 3; kHessR 0 c r s 0 1, kHessR 0 c r s 1 1, kHessR 0 c r s 1 2, kHessR 0 c r s 1 3; kHessR 0 c r s 0 2, kHessR 0 c r s 1 2, kHessR 0 c r s 2 2, kHessR 0 c r s 2 3; kHessR 0 c r s 0 3, kHessR 0 c r s 1 3, kHessR 0 c r s 2 3, kHessR 0 c r s 3 3] * (!![kGradR 0 c r s 2, kGradR 0 c r s 3, -kGradR 0 c r s 0, -kGradR 0 c r s 1; kGradR 0 c r s 1, -kGradR 0 c r s 0, -kGradR 0 c r s 3, kGradR 0 c r s 2; -kGradR 0 c r s 3, kGradR 0 c r s 2, -kGradR 0 c r s 1, kGradR 0 c r s 0] : Matrix (Fin 3) (Fin 4) ℝ).transpose := by
  have hsym : ∀ i j, kHessR 0 c r s i j = kHessR 0 c r s j i := by
    intro i j
    fin_cases i <;> fin_cases j <;> simp [kHessR, hP, TangentialHessian.hZ, hD, dZ, dD] <;> ring
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tHessR, frameHess, frame, qI, qJ, qK, Matrix.mul_apply, Fin.sum_univ_four,
      Fin.sum_univ_three, Matrix.mulVec, dotProduct, Matrix.transpose_apply,
      hsym 1 0, hsym 2 0, hsym 3 0, hsym 2 1, hsym 3 1, hsym 3 2] <;> ring
