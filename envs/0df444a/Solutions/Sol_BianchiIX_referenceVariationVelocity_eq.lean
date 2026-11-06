-- Prove2me | solution 1 for BianchiIX.referenceVariationVelocity_eq
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:59:12.455526+00:00
-- url     : https://prove2.me/submissions/6b459275-bd11-4134-856b-afe4bcc1ade0

import Definitions.Def_BianchiIX_Dynamics_ProjectiveLinearization
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Theorems.Thm_BianchiIX_projectiveField_boundary_fderiv
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


theorem solution (k t a : ℝ) (xi : ProjectiveState) :
    referenceVariationVelocity k t xi a =
      projectiveBoundaryVariation (referencePulse k t 0) (referencePulse k t 2) xi +
        a • projectiveField (referencePulse k t) := by
  unfold referenceVariationVelocity
  rw [show fderiv ℝ projectiveField (referencePulse k t) xi = _ from
    projectiveField_boundary_fderiv _ _ _]
  rfl
