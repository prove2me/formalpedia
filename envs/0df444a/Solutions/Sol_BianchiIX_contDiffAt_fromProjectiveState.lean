-- Prove2me | solution 1 for BianchiIX.contDiffAt_fromProjectiveState
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:29:25.682883+00:00
-- url     : https://prove2.me/submissions/eb78cb0c-eddd-4e43-9d6a-95c2a4b8d592

import Definitions.Def_BianchiIX_Dynamics_ProjectiveRegularity
import Theorems.Thm_BianchiIX_contDiff_projectiveStateDenom
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


theorem solution (n : WithTop ℕ∞) {y : ProjectiveState}
    (hD : projectiveStateDenom y ≠ 0) : ContDiffAt ℝ n fromProjectiveState y := by
  have hden := (contDiff_projectiveStateDenom n).contDiffAt (x := y)
  apply contDiffAt_pi.mpr
  intro i
  fin_cases i <;> dsimp [fromProjectiveState] <;> fun_prop
