-- Prove2me | solution 1 for BianchiIX.contDiff_stateConstraint
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T13:55:38.008213+00:00
-- url     : https://prove2.me/submissions/3ffabd9f-e7de-4eca-8dcb-e82caa3c11e1

import Definitions.Def_BianchiIX_Dynamics_Normalized
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

noncomputable section
open BianchiIX
open Set


theorem solution (n : WithTop ℕ∞) : ContDiff ℝ n stateConstraint := by
  unfold stateConstraint constraint shearSq curvature
  fun_prop
