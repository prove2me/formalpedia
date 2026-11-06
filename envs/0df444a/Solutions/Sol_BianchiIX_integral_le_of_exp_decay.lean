-- Prove2me | solution 1 for BianchiIX.integral_le_of_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:35:59.553208+00:00
-- url     : https://prove2.me/submissions/ff399b3a-619c-4e28-95ef-5719d0afa6cb

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

namespace BianchiIX
end BianchiIX

noncomputable section
open BianchiIX
open Set MeasureTheory

private theorem BianchiIX.integral_exp_decay_le {a b c : ℝ} (hc : 0 < c) :
    (∫ z in a..b, Real.exp (-c * (z - a))) ≤ 1 / c := by
  rw [integral_exp_decay hc]
  exact (div_le_div_iff_of_pos_right hc).mpr (by linarith [Real.exp_pos (-c * (b - a))])

theorem solution {f : ℝ → ℝ} {a b c B : ℝ} (hab : a ≤ b) (hc : 0 < c)
    (hB : 0 ≤ B) (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ z ∈ Icc a b, f z ≤ B * Real.exp (-c * (z - a))) :
    (∫ z in a..b, f z) ≤ B / c := by
  have hg : Continuous (fun z => B * Real.exp (-c * (z - a))) := by fun_prop
  have H := intervalIntegral.integral_mono_on (μ := volume) hab
    (hf.intervalIntegrable_of_Icc hab) (hg.intervalIntegrable _ _) hbound
  rw [intervalIntegral.integral_const_mul] at H
  exact H.trans ((mul_le_mul_of_nonneg_left (integral_exp_decay_le hc) hB).trans_eq (by ring))
