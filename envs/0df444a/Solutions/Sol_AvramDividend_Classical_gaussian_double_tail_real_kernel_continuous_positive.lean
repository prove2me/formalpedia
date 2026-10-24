-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_double_tail_real_kernel_continuous_positive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T13:53:49.797265+00:00
-- url     : https://prove2.me/submissions/a18b5fe9-1431-48d6-b63b-fa30d885aa69

import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_kernel_finite_positive

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The finite double-tail kernel is continuous after conversion to real values. -/
theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤)
    (t : ℝ) (ht : 0 < t) :
    ContinuousAt (fun u : ℝ => (∫⁻ z : ℝ,
      (if 0 < u ∧ u < z then
        ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ).toReal) t := by
  let K : ℝ → ENNReal := fun u : ℝ =>
    ∫⁻ z : ℝ,
      (if 0 < u ∧ u < z then
        ENNReal.ofReal (z - u) * ENNReal.ofReal (Real.exp (-φ * z))
       else 0) ∂μ
  have hcont : ContinuousAt K t :=
    AvramDividend.Classical.gaussian_double_tail_kernel_continuous_positive
      μ φ hφ hlevy t ht
  have hfin : K t ≠ ⊤ :=
    ne_of_lt (AvramDividend.Classical.gaussian_double_tail_kernel_finite_positive
      μ φ hφ hlevy t ht)
  change ContinuousAt (fun u : ℝ => (K u).toReal) t
  exact (ENNReal.continuousAt_toReal hfin).comp hcont
