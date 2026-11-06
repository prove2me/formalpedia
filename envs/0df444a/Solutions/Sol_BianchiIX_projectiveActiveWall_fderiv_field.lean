-- Prove2me | solution 1 for BianchiIX.projectiveActiveWall_fderiv_field
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:34:48.957425+00:00
-- url     : https://prove2.me/submissions/f76e4605-58b4-4e33-81a5-17a266a46db9

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Theorems.Thm_BianchiIX_projectiveActiveWall_fderiv
import Theorems.Thm_BianchiIX_toProjectiveState_fderiv_field
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
    (hA : 1 + x 0 ≠ 0) (hc : stateConstraint x = 1) :
    fderiv ℝ projectiveActiveWall x (normalizedField x) =
      (1 + x 0) * projectiveField (toProjectiveState x) 2 := by
  rw [projectiveActiveWall_fderiv hA]
  rw [toProjectiveState_fderiv_field hA hc]
  rfl
