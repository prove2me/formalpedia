-- Prove2me | solution 1 for BianchiIX.toProjectiveState_positive
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:22:49.490517+00:00
-- url     : https://prove2.me/submissions/ae0e54c4-9e4b-4e69-a057-602580fcd21d

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


theorem solution {x : NormalizedState}
    (hA : 0 < 1 + x 0) (hx : positiveWalls x) :
    0 < toProjectiveState x 1 ∧ 0 < toProjectiveState x 2 ∧ 0 < toProjectiveState x 3 := by
  have hr : 0 < Real.sqrt 3 := Real.sqrt_pos.mpr (by norm_num)
  exact ⟨div_pos (mul_pos hr hx.1) hA, div_pos (mul_pos hr hx.2.1) hA,
    div_pos (mul_pos hr hx.2.2) hA⟩
