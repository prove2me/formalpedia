-- Prove2me | solution 1 for BianchiIX.referencePulse_denom
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:53:43.043493+00:00
-- url     : https://prove2.me/submissions/c218c034-45ec-446b-99d6-a7ec7fa4f411

import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Theorems.Thm_BianchiIX_referencePulse_energy
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
    projectiveStateDenom (referencePulse k t) = k ^ 2 + 4 - 2 * k * Real.tanh (k * t) := by
  have he := referencePulse_energy k t
  dsimp [projectiveStateDenom, projectiveDenom, referencePulse, curvature, coreEnergy] at *
  nlinarith only [he]
