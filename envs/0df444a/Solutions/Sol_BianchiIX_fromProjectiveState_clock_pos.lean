-- Prove2me | solution 1 for BianchiIX.fromProjectiveState_clock_pos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:22:02.449902+00:00
-- url     : https://prove2.me/submissions/602a30d1-e586-4399-a307-c12fceab8b71

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
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


theorem solution {y : ProjectiveState}
    (hD : 0 < projectiveStateDenom y) : 0 < 1 + fromProjectiveState y 0 := by
  change 0 < 1 + (6 / projectiveStateDenom y - 1)
  linarith [div_pos (show (0 : ℝ) < 6 by norm_num) hD]
