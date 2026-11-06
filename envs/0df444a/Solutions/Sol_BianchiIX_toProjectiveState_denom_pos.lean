-- Prove2me | solution 1 for BianchiIX.toProjectiveState_denom_pos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:30:53.949441+00:00
-- url     : https://prove2.me/submissions/bc10a80f-1f82-4f3a-97f2-712e1edecbbc

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_projectiveDenom_positive
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
    (hA : 0 < 1 + x 0) (hc : stateConstraint x = 1) :
    0 < projectiveStateDenom (toProjectiveState x) :=
  projectiveDenom_positive hA hc
