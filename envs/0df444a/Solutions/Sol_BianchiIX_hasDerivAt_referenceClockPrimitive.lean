-- Prove2me | solution 1 for BianchiIX.hasDerivAt_referenceClockPrimitive
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-04T21:58:20.480201+00:00
-- url     : https://prove2.me/submissions/7998c8fb-d39a-4017-bf99-73a66cb1550a

import Definitions.Def_BianchiIX_Dynamics_ProjectiveState
import Definitions.Def_BianchiIX_Dynamics_ReferencePulse
import Definitions.Def_BianchiIX_Dynamics_ReferenceReturn
import Theorems.Thm_BianchiIX_referencePulse_denom
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


theorem solution (k t : ℝ) :
    HasDerivAt (referenceClockPrimitive k) (projectiveStateDenom (referencePulse k t) / 6) t := by
  have hz : HasDerivAt (fun s : ℝ => k * s) k t := by
    simpa using (hasDerivAt_id t).const_mul k
  have hlog := (hz.cosh.log (ne_of_gt (Real.cosh_pos (k * t)))).div_const 3
  convert! (((hasDerivAt_id t).const_mul (k ^ 2 + 4)).div_const 6).sub hlog using 1
  · rw [referencePulse_denom, Real.tanh_eq_sinh_div_cosh]
    ring
