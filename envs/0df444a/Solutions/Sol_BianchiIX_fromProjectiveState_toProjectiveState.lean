-- Prove2me | solution 1 for BianchiIX.fromProjectiveState_toProjectiveState
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:30:27.923909+00:00
-- url     : https://prove2.me/submissions/5169281b-6fe4-43b2-a9c8-65300efca68e

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_projective_inverse_coord
import Theorems.Thm_BianchiIX_projective_inverse_scale
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
    fromProjectiveState (toProjectiveState x) = x := by
  have hscale : 6 / projectiveStateDenom (toProjectiveState x) = 1 + x 0 :=
    projective_inverse_scale hA hc
  unfold fromProjectiveState
  rw [hscale]
  ext i
  fin_cases i
  · change 1 + x 0 - 1 = x 0
    ring
  all_goals exact projective_inverse_coord hA
