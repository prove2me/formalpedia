-- Prove2me | solution 1 for AvramDividend.Classical.positiveLaplace_lintegral_conv
-- status  : ACCEPTED   (prove)
-- author  : @Nickrobbins95
-- created : 2026-10-04T03:30:59.649982+00:00
-- url     : https://prove2.me/submissions/c0a26d8c-752a-4b18-adc6-5af438b5280f

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

open MeasureTheory Set in
theorem solution (μ ν : Measure ℝ) [SFinite ν] (θ : ℝ) :
    (∫⁻ z : ℝ, ENNReal.ofReal (Real.exp (-θ * z)) ∂(μ ∗ ν)) =
      (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-θ * x)) ∂μ) *
        (∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-θ * y)) ∂ν) := by
  have hf : Measurable (fun z : ℝ => ENNReal.ofReal (Real.exp (-θ * z))) := by fun_prop
  rw [Measure.lintegral_conv hf]
  have key : ∀ x y : ℝ, ENNReal.ofReal (Real.exp (-θ * (x + y))) =
      ENNReal.ofReal (Real.exp (-θ * x)) * ENNReal.ofReal (Real.exp (-θ * y)) := by
    intro x y
    rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]
    congr 2
    ring
  simp_rw [key]
  have hg : Measurable (fun y : ℝ => ENNReal.ofReal (Real.exp (-θ * y))) := by fun_prop
  simp_rw [lintegral_const_mul _ hg]
  rw [lintegral_mul_const _ (by fun_prop)]
