-- Prove2me | solution 1 for BianchiIX.hasDerivAt_referenceOriginalVariation
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:02:40.324257+00:00
-- url     : https://prove2.me/submissions/f655926b-fa64-407d-9ff1-f276fecb9d55

import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ReferenceScattering
import Definitions.Def_BianchiIX_Dynamics_ProjectiveOriginalTime
import Theorems.Thm_BianchiIX_referenceOriginalVariation_identity
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


/-- Rescale an original-time variational solution using the reference clock. -/
theorem solution {k t : ℝ} {xi : ℝ → ProjectiveState}
    {clock : ℝ → ℝ}
    (hxi : HasDerivAt xi
      (fderiv ℝ projectiveOriginalField (referencePulse k t) (xi (clock t))) (clock t))
    (hc : HasDerivAt clock (projectiveStateDenom (referencePulse k t) / 6) t) :
    HasDerivAt (fun s => xi (clock s))
      (referenceVariationVelocity k t (xi (clock t))
        (-fderiv ℝ projectiveStateDenom (referencePulse k t) (xi (clock t)) /
          projectiveStateDenom (referencePulse k t))) t := by
  have H := hxi.scomp t hc
  rw [referenceOriginalVariation_identity] at H
  exact H
