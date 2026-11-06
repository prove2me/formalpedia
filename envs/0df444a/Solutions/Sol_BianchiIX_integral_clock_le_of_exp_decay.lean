-- Prove2me | solution 1 for BianchiIX.integral_clock_le_of_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T02:28:59.23496+00:00
-- url     : https://prove2.me/submissions/dde78be2-69e2-4098-8ce8-9bcb9db4746a

import Theorems.Thm_BianchiIX_integral_clock_le_envelope
import Theorems.Thm_BianchiIX_integral_exp_decay
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import Mathlib.Analysis.SpecialFunctions.Arsinh
import Mathlib.Analysis.SpecialFunctions.Sqrt
import Mathlib.Tactic.FieldSimp
import Mathlib.Analysis.Calculus.ContDiff.Operations
import Mathlib.Analysis.Calculus.Deriv.Prod
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic.FinCases
import Mathlib.Tactic.FunProp
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.Tactic.LinearCombination
import Mathlib.Analysis.SpecialFunctions.Arcosh
import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Mathlib.Analysis.Calculus.InverseFunctionTheorem.Deriv
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Analysis.SpecialFunctions.Pow.Deriv
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.Analysis.ODE.ExistUnique
import Mathlib.Analysis.Calculus.FDeriv.Partial
import Mathlib.MeasureTheory.Integral.IntervalIntegral.DistLEIntegral
import Mathlib.MeasureTheory.Integral.IntervalIntegral.IntegrationByParts

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

section
noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_exp_decay_le {a b c : ℝ} (hc : 0 < c) :
    (∫ z in a..b, Real.exp (-c * (z - a))) ≤ 1 / c := by
  rw [integral_exp_decay hc]
  exact (div_le_div_iff_of_pos_right hc).mpr (by linarith [Real.exp_pos (-c * (b - a))])

end
end

theorem solution {f z rate : ℝ → ℝ} {a b c B : ℝ}
    (hab : a ≤ b) (hz : ∀ t ∈ Icc a b, HasDerivAt z (rate t) t)
    (hrate : ContinuousOn rate (Icc a b)) (hpos : ∀ t ∈ Icc a b, 0 ≤ rate t)
    (hc : 0 < c) (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f t ≤ B * Real.exp (-c * (z t - z a))) :
    (∫ t in a..b, f t * rate t) ≤ B / c := by
  have hG : Continuous (fun s => B * Real.exp (-c * (s - z a))) := by fun_prop
  have H := integral_clock_le_envelope hab hz hrate hpos hf hG hbound
  rw [intervalIntegral.integral_const_mul] at H
  exact H.trans ((mul_le_mul_of_nonneg_left (integral_exp_decay_le hc) hB).trans_eq (by ring))
