-- Prove2me | solution 1 for BianchiIX.fromProjectiveState_constraint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:31:20.033705+00:00
-- url     : https://prove2.me/submissions/f1cb778b-37cf-465a-9b3d-bcca68c0a76a

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Theorems.Thm_BianchiIX_constraint_of_inverse_projective
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
    (hD : projectiveStateDenom y ≠ 0) : stateConstraint (fromProjectiveState y) = 1 :=
  constraint_of_inverse_projective hD
