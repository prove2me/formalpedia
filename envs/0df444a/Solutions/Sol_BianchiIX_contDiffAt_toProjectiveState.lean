-- Prove2me | solution 1 for BianchiIX.contDiffAt_toProjectiveState
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:26:06.014353+00:00
-- url     : https://prove2.me/submissions/94b2d9dc-60f1-4cd7-9fd0-22c8d2b9947a

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
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


theorem solution (n : WithTop ℕ∞) {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) : ContDiffAt ℝ n toProjectiveState x := by
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [toProjectiveState, projectiveCoord] <;> fun_prop
