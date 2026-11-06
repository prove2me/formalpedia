-- Prove2me | solution 1 for BianchiIX.projectiveActiveWall_fderiv
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:29:56.410679+00:00
-- url     : https://prove2.me/submissions/3e0e780e-359b-4ea3-bb2d-01b0a649a139

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Theorems.Thm_BianchiIX_contDiffAt_toProjectiveState
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

noncomputable section
open BianchiIX


theorem solution {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) (v : NormalizedState) :
    fderiv ℝ projectiveActiveWall x v = (fderiv ℝ toProjectiveState x v) 2 := by
  have hd := (hasFDerivAt_apply (𝕜 := ℝ) (2 : Fin 4) (toProjectiveState x)).comp x
    ((contDiffAt_toProjectiveState 1 hA).differentiableAt (by norm_num)).hasFDerivAt
  rw [show fderiv ℝ projectiveActiveWall x = _ from hd.fderiv]
  rfl
