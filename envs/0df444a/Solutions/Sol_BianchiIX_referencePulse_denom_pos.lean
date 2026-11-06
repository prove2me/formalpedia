-- Prove2me | solution 1 for BianchiIX.referencePulse_denom_pos
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:46:34.602067+00:00
-- url     : https://prove2.me/submissions/20e1bf2e-853b-435f-a7c5-83bd69a1bce3

import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
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
import Mathlib.Analysis.SpecialFunctions.Arcosh

noncomputable section
open BianchiIX


theorem solution (k t : ℝ) :
    0 < projectiveStateDenom (referencePulse k t) := by
  dsimp [projectiveStateDenom, projectiveDenom, referencePulse, curvature]
  nlinarith only [sq_nonneg (1 - k * Real.tanh (k * t)), sq_nonneg (k / Real.cosh (k * t))]
