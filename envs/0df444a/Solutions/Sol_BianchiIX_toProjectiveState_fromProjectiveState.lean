-- Prove2me | solution 1 for BianchiIX.toProjectiveState_fromProjectiveState
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:26:59.673198+00:00
-- url     : https://prove2.me/submissions/4e562a62-f8c4-4ebf-9d78-01243aa9cfb2

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_projective_forward_coord
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
    (hD : projectiveStateDenom y ≠ 0) :
    toProjectiveState (fromProjectiveState y) = y := by
  have hA : 6 / projectiveStateDenom y ≠ 0 := div_ne_zero (by norm_num) hD
  ext i
  fin_cases i <;> exact projective_forward_coord hA
