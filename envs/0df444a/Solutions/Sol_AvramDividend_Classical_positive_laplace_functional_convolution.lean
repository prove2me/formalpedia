-- Prove2me | solution 1 for AvramDividend.Classical.positive_laplace_functional_convolution
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:42:49.249771+00:00
-- url     : https://prove2.me/submissions/e611ea92-0c89-4178-b975-0606b18ff73d

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

open MeasureTheory Set in
theorem solution (μ ν : Measure ℝ) [SFinite ν] (θ : ℝ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-θ * z))
       ∂Measure.conv μ ν) =
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂μ) *
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-θ * y)) ∂ν) := by
  have hf : Measurable fun z : ℝ => ENNReal.ofReal (Real.exp (-θ * z)) := by fun_prop
  rw [Measure.lintegral_conv hf]
  have h : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (-θ * (x + y))) =
      ENNReal.ofReal (Real.exp (-θ * x)) * ENNReal.ofReal (Real.exp (-θ * y)) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  simp_rw [h]
  rw [← lintegral_mul_const _ (by fun_prop)]
  refine lintegral_congr fun x => ?_
  rw [lintegral_const_mul _ (by fun_prop)]

