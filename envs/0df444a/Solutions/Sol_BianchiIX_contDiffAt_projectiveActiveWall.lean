-- Prove2me | solution 1 for BianchiIX.contDiffAt_projectiveActiveWall
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:29:41.502258+00:00
-- url     : https://prove2.me/submissions/8f097638-c5e1-44f6-9d26-7fe607d015d5

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


theorem solution (n : WithTop ℕ∞) {x : NormalizedState}
    (hA : 1 + x 0 ≠ 0) : ContDiffAt ℝ n projectiveActiveWall x :=
  contDiffAt_pi.mp (contDiffAt_toProjectiveState n hA) 2
