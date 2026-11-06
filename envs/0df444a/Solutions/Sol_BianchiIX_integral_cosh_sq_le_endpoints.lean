-- Prove2me | solution 1 for BianchiIX.integral_cosh_sq_le_endpoints
-- status  : ACCEPTED   (prove)
-- author  : @trppppp
-- created : 2026-11-05T00:33:14.833697+00:00
-- url     : https://prove2.me/submissions/492f2c0f-7fcb-45b5-9d4a-229e513f557c

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


/-- Endpoint control replaces an enclosing arcosh interval in the slow-wall integral. -/
theorem solution {a b : ℝ} (hab : a ≤ b) :
    (∫ z in a..b, Real.cosh z ^ 2) ≤ Real.cosh a ^ 2 + Real.cosh b ^ 2 := by
  have hd (z : ℝ) : HasDerivAt (fun u => Real.sinh u * Real.cosh u)
      (Real.cosh z ^ 2 + Real.sinh z ^ 2) z := by
    convert! (Real.hasDerivAt_sinh z).mul (Real.hasDerivAt_cosh z) using 1
    ring
  have hc : Continuous (fun z => Real.cosh z ^ 2 + Real.sinh z ^ 2) := by fun_prop
  have hcosh : Continuous (fun z => Real.cosh z ^ 2) := by fun_prop
  have H := intervalIntegral.integral_mono_on (μ := volume) hab (hcosh.intervalIntegrable _ _) (hc.intervalIntegrable _ _)
    (fun z _ => le_add_of_nonneg_right (sq_nonneg (Real.sinh z)))
  rw [intervalIntegral.integral_eq_sub_of_hasDerivAt (fun z _ => hd z) (hc.intervalIntegrable _ _)] at H
  have hb := mul_le_mul_of_nonneg_right (Real.sinh_lt_cosh (x := b)).le (Real.cosh_pos b).le
  have ha := mul_le_mul_of_nonneg_right
    (show -Real.sinh a ≤ Real.cosh a by
      simpa only [Real.sinh_neg, Real.cosh_neg] using (Real.sinh_lt_cosh (x := -a)).le) (Real.cosh_pos a).le
  nlinarith
