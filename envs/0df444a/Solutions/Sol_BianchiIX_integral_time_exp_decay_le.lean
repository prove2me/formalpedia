-- Prove2me | solution 1 for BianchiIX.integral_time_exp_decay_le
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:54:37.262464+00:00
-- url     : https://prove2.me/submissions/91fa01ab-48d3-4f5e-ad0f-305b0ac20bad

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


theorem solution {a b c : ℝ} (hab : a ≤ b) (hc : 0 < c) :
    (∫ t in a..b, (t - a) * Real.exp (-c * (t - a))) ≤ 1 / c ^ 2 := by
  have hd (t : ℝ) : HasDerivAt (fun s => -((s - a) / c + 1 / c ^ 2) * Real.exp (-c * (s - a)))
      ((t - a) * Real.exp (-c * (t - a))) t := by
    convert! ((((hasDerivAt_id t).sub_const a).div_const c).add_const (1 / c ^ 2)).neg.mul
      (((hasDerivAt_id t).sub_const a).const_mul (-c)).exp using 1
    dsimp
    field_simp
    ring
  have hcont : Continuous (fun t => (t - a) * Real.exp (-c * (t - a))) := by fun_prop
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun t _ => hd t) (hcont.intervalIntegrable _ _)]
  simp only [sub_self, zero_div, zero_add, mul_zero, Real.exp_zero, mul_one]
  have hnonneg : 0 ≤ ((b - a) / c + 1 / c ^ 2) * Real.exp (-c * (b - a)) :=
    mul_nonneg (add_nonneg (div_nonneg (sub_nonneg.mpr hab) hc.le) (by positivity)) (Real.exp_pos _).le
  linarith only [hnonneg]
