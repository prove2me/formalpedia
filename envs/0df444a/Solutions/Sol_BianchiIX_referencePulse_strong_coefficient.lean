-- Prove2me | solution 1 for BianchiIX.referencePulse_strong_coefficient
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:54:10.012092+00:00
-- url     : https://prove2.me/submissions/af7a34c3-e814-4bee-8a8e-c8c3e211b541

import Definitions.Def_BianchiIX_Algebra_Projective
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ReferenceVariation
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
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique

noncomputable section
open BianchiIX
open Set


theorem solution (k t : ℝ) :
    (1 - (referencePulse k t 0) ^ 2 - (referencePulse k t 2) ^ 2) / 2 =
      -(k ^ 2 / 2) + k * Real.tanh (k * t) := by
  have he := referencePulse_energy k t
  dsimp [coreEnergy, referencePulse] at *
  nlinarith only [he]
