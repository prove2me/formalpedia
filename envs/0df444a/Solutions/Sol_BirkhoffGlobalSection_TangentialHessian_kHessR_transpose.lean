-- Prove2me | solution 1 for BirkhoffGlobalSection.TangentialHessian.kHessR_transpose
-- status  : ACCEPTED   (prove)
-- author  : @Mazecto
-- created : 2026-09-29T22:45:16.125529+00:00
-- url     : https://prove2.me/submissions/be72c8f7-e457-4ebe-9376-c3ad39930bd3

import Definitions.Def_BirkhoffGlobalSection_TangentialHessian
import Mathlib.Tactic.Ring
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Positivity
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FieldSimp

open Matrix in
open BirkhoffGlobalSection BirkhoffGlobalSection.TangentialHessian in
theorem solution (μ c r : ℝ) (s : Phase) : (kHessR μ c r s).transpose = kHessR μ c r s := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [kHessR, Matrix.transpose_apply] <;>
    simp [hP, hZ, hD, dZ, dD] <;> (try ring_nf) <;> simp
