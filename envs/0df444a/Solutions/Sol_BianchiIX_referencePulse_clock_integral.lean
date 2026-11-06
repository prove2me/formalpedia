-- Prove2me | solution 1 for BianchiIX.referencePulse_clock_integral
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:01:02.835532+00:00
-- url     : https://prove2.me/submissions/c2b5c395-f17f-487d-913b-8b5adc7c95fe

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Theorems.Thm_BianchiIX_continuous_projectiveStateDenom
import Theorems.Thm_BianchiIX_hasDerivAt_referenceClockPrimitive
import Theorems.Thm_BianchiIX_hasDerivAt_referencePulse
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
open Set MeasureTheory


theorem solution (k a b : ℝ) :
    integralClock (fun t => projectiveStateDenom (referencePulse k t) / 6) a b =
      referenceClockPrimitive k b - referenceClockPrimitive k a := by
  apply intervalIntegral.integral_eq_sub_of_hasDerivAt
    (fun t _ => hasDerivAt_referenceClockPrimitive k t)
  have hc : Continuous (referencePulse k) :=
    continuous_iff_continuousAt.mpr (fun t => (hasDerivAt_referencePulse k t).continuousAt)
  exact ((continuous_projectiveStateDenom.comp hc).div_const 6).intervalIntegrable _ _
