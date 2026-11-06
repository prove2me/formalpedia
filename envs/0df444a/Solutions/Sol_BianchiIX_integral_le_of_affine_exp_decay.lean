-- Prove2me | solution 1 for BianchiIX.integral_le_of_affine_exp_decay
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T01:56:20.170275+00:00
-- url     : https://prove2.me/submissions/24dc9d6f-121b-4f3e-9e72-1b86f486a9b5

import Theorems.Thm_BianchiIX_integral_exp_decay
import Theorems.Thm_BianchiIX_integral_time_exp_decay_le
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

theorem solution {f : ℝ → ℝ} {a b c A B : ℝ}
    (hab : a ≤ b) (hc : 0 < c) (hA : 0 ≤ A) (hB : 0 ≤ B)
    (hf : ContinuousOn f (Icc a b))
    (hbound : ∀ t ∈ Icc a b, f t ≤ Real.exp (-c * (t - a)) * (A + B * (t - a))) :
    (∫ t in a..b, f t) ≤ A / c + B / c ^ 2 := by
  have h0 : Continuous (fun t => A * Real.exp (-c * (t - a))) := by fun_prop
  have h1 : Continuous (fun t => B * ((t - a) * Real.exp (-c * (t - a)))) := by fun_prop
  have H := intervalIntegral.integral_mono_on (μ := volume) hab
    (hf.intervalIntegrable_of_Icc hab) ((h0.add h1).intervalIntegrable _ _)
    (fun t ht => (hbound t ht).trans_eq (by dsimp; ring))
  simp only [Pi.add_apply] at H
  rw [intervalIntegral.integral_add (h0.intervalIntegrable _ _) (h1.intervalIntegrable _ _),
    intervalIntegral.integral_const_mul, intervalIntegral.integral_const_mul] at H
  apply H.trans
  have H' := add_le_add (mul_le_mul_of_nonneg_left (integral_exp_decay_le (a := a) (b := b) hc) hA)
    (mul_le_mul_of_nonneg_left (integral_time_exp_decay_le hab hc) hB)
  convert! H' using 1
  ring
