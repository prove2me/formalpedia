-- Prove2me | solution 1 for BianchiIX.fromProjectiveState_positive
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:23:25.967827+00:00
-- url     : https://prove2.me/submissions/a21b8c38-1b78-446f-a52d-6c4f6303e056

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
    (hD : 0 < projectiveStateDenom y) (hy : 0 < y 1 ∧ 0 < y 2 ∧ 0 < y 3) :
    positiveWalls (fromProjectiveState y) := by
  have hA : 0 < 6 / projectiveStateDenom y := div_pos (by norm_num) hD
  have hr : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  exact ⟨div_pos (mul_pos hA hy.1) hr, div_pos (mul_pos hA hy.2.1) hr,
    div_pos (mul_pos hA hy.2.2) hr⟩
