-- Prove2me | solution 1 for AvramDividend.Classical.chat07_weighted_compensated_jump_integral_triangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:08:33.769692+00:00
-- url     : https://prove2.me/submissions/26ab1a6d-22a1-4005-8fb4-954625cfa93f

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Analysis.Calculus.Deriv.Slope
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.MeasureTheory.Integral.IntegrableOn
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Theorems.Thm_AvramDividend_Classical_chat07_weighted_compensated_negative_jump_abs_le
import Mathlib.Tactic.Ring

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-! Integrating the pointwise compensated negative-jump triangle bound. -/
theorem solution
    (W : ℝ → ℝ) (hW : Monotone W)
    (θ r : ℝ) (hr : 0 ≤ r)
    (hker : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        |W (x-r) - W x + r * deriv W x|) (Ioi (0 : ℝ)))
    (hshift : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) *
        |W x - W (x-r)|) (Ioi (0 : ℝ)))
    (hderiv : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ * x)) * deriv W x)
      (Ioi (0 : ℝ))) :
    (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        |W (x-r) - W x + r * deriv W x|) ≤
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ * x)) *
        |W x - W (x-r)|) +
      r * (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ * x)) * deriv W x) := by
  have hpoint : ∀ x : ℝ,
      Real.exp (-(θ * x)) *
        |W (x-r) - W x + r * deriv W x| ≤
      Real.exp (-(θ * x)) * |W x - W (x-r)| +
        r * (Real.exp (-(θ * x)) * deriv W x) := by
    intro x
    have hmono : 0 ≤ W x - W (x-r) :=
      sub_nonneg.mpr (hW (sub_le_self x hr))
    calc
      _ ≤ Real.exp (-(θ*x)) *
          ((W x - W (x-r)) + r*deriv W x) :=
        AvramDividend.Classical.chat07_weighted_compensated_negative_jump_abs_le
          W hW θ x r hr
      _ = Real.exp (-(θ*x)) * |W x - W (x-r)| +
          r*(Real.exp (-(θ*x))*deriv W x) := by
        rw [abs_of_nonneg hmono]
        ring
  have hsum : IntegrableOn
      (fun x : ℝ => Real.exp (-(θ*x)) * |W x - W (x-r)| +
        r * (Real.exp (-(θ*x)) * deriv W x))
      (Ioi (0 : ℝ)) :=
    hshift.add (hderiv.const_mul r)
  have hmono :
      (∫ x in Ioi (0 : ℝ), Real.exp (-(θ*x)) *
        |W (x-r) - W x + r * deriv W x|) ≤
      (∫ x in Ioi (0 : ℝ),
        Real.exp (-(θ*x)) * |W x - W (x-r)| +
        r * (Real.exp (-(θ*x)) * deriv W x)) :=
    integral_mono hker hsum hpoint
  calc
    _ ≤ (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ*x))*|W x - W (x-r)| +
          r*(Real.exp (-(θ*x))*deriv W x)) := hmono
    _ = (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ*x))*|W x - W (x-r)|) +
        r * (∫ x in Ioi (0 : ℝ),
          Real.exp (-(θ*x))*deriv W x) := by
      rw [MeasureTheory.integral_add hshift (hderiv.const_mul r)]
      rw [MeasureTheory.integral_const_mul]
