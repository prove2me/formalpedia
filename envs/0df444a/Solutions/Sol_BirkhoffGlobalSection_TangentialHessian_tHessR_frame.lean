-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.tHessR_frame
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:45:26.765339+00:00
-- url     : https://prove2.me/submissions/7e059e9b-e4dd-486b-b9ef-abd0b08900cc

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Theorems.Thm_BirkhoffGlobalSection_TangentialHessian_kHessR_transpose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

set_option maxRecDepth 20000
set_option maxHeartbeats 1000000

open Matrix in
open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian in
theorem solution (μ c r : ℝ) (s : Phase) :
    tHessR μ c r s = !![kGradR μ c r s 2, kGradR μ c r s 3, -kGradR μ c r s 0, -kGradR μ c r s 1;
        kGradR μ c r s 1, -kGradR μ c r s 0, -kGradR μ c r s 3, kGradR μ c r s 2;
        -kGradR μ c r s 3, kGradR μ c r s 2, -kGradR μ c r s 1, kGradR μ c r s 0] *
      !![kHessR μ c r s 0 0, kHessR μ c r s 0 1, kHessR μ c r s 0 2, kHessR μ c r s 0 3;
        kHessR μ c r s 0 1, kHessR μ c r s 1 1, kHessR μ c r s 1 2, kHessR μ c r s 1 3;
        kHessR μ c r s 0 2, kHessR μ c r s 1 2, kHessR μ c r s 2 2, kHessR μ c r s 2 3;
        kHessR μ c r s 0 3, kHessR μ c r s 1 3, kHessR μ c r s 2 3, kHessR μ c r s 3 3] *
      (!![kGradR μ c r s 2, kGradR μ c r s 3, -kGradR μ c r s 0, -kGradR μ c r s 1;
        kGradR μ c r s 1, -kGradR μ c r s 0, -kGradR μ c r s 3, kGradR μ c r s 2;
        -kGradR μ c r s 3, kGradR μ c r s 2, -kGradR μ c r s 1, kGradR μ c r s 0] :
          Matrix (Fin 3) (Fin 4) ℝ).transpose := by
  have hsym : ∀ i j, kHessR μ c r s i j = kHessR μ c r s j i := fun i j => by
    simpa [Matrix.transpose_apply] using congrFun (congrFun (kHessR_transpose μ c r s) j) i
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [tHessR, frameHess, frame, qI, qJ, qK, Matrix.mul_apply, Fin.sum_univ_four,
      dotProduct, Matrix.transpose_apply,
      hsym 1 0, hsym 2 0, hsym 3 0, hsym 2 1, hsym 3 1, hsym 3 2] <;> ring
