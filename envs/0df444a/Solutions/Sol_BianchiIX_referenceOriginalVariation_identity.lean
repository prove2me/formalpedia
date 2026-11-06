-- Prove2me | solution 1 for BianchiIX.referenceOriginalVariation_identity
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:00:36.493203+00:00
-- url     : https://prove2.me/submissions/974f4ccb-3bb6-461f-8010-df17ab961b23

import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Theorems.Thm_BianchiIX_projectiveOriginalField_fderiv
import Theorems.Thm_BianchiIX_referencePulse_denom_pos
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


theorem solution (k t : ℝ) (xi : ProjectiveState) :
    (projectiveStateDenom (referencePulse k t) / 6) •
        fderiv ℝ projectiveOriginalField (referencePulse k t) xi =
      referenceVariationVelocity k t xi
        (-fderiv ℝ projectiveStateDenom (referencePulse k t) xi /
          projectiveStateDenom (referencePulse k t)) := by
  have hD := ne_of_gt (referencePulse_denom_pos k t)
  rw [projectiveOriginalField_fderiv hD]
  ext i
  dsimp [referenceVariationVelocity]
  field_simp
  ring
