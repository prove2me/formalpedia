-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_kernel_local_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-21T20:43:56.912471+00:00
-- url     : https://prove2.me/submissions/e0dfce6c-f1a5-4099-a4ba-7be35a60db79

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_antitone
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_finite_positive
import Mathlib.Analysis.Complex.Exponential

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
open AvramDividend.Classical

/-- On every time interval bounded away from zero, the integrated Gaussian
double-tail kernel is bounded by a finite value at the left endpoint. -/
theorem solution (μ : Measure ℝ) [SFinite μ] (φ δ t : ℝ)
    (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (hδ : 0 < δ) (hδt : δ ≤ t) :
    (∫⁻ z : ℝ,
      (if 0 < t ∧ t < z then
        ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) ≤
    (∫⁻ z : ℝ,
      (if 0 < δ ∧ δ < z then
        ENNReal.ofReal (z - δ) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) ∧
    (∫⁻ z : ℝ,
      (if 0 < δ ∧ δ < z then
        ENNReal.ofReal (z - δ) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ) < ⊤ := by
  constructor
  · exact gaussian_double_tail_kernel_antitone μ φ δ t hδ hδt
  · exact gaussian_double_tail_kernel_finite_positive μ φ hφ hlevy δ hδ
