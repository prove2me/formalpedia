-- Prove2me | solution 1 for BianchiIX.referencePulse_crossing_time
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T22:03:05.862914+00:00
-- url     : https://prove2.me/submissions/d61e5df6-7ffe-4b97-a465-0eb1ca5038dd

import Definitions.Def_BianchiIX_Dynamics_IntegralClock
import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Theorems.Thm_BianchiIX_referencePulse_clock_integral
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


theorem solution (k : ℝ) :
    integralClock (fun t => projectiveStateDenom (referencePulse k t) / 6)
      (-referenceHalfTime k) (referenceHalfTime k) = referenceNormalizedTime k := by
  rw [referencePulse_clock_integral]
  simp only [referenceClockPrimitive, referenceNormalizedTime, mul_neg, Real.cosh_neg]
  unfold referenceHalfTime
  ring
