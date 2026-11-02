-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_02c_nested_absolute_l1_implies_product_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:53:39.505208+00:00
-- url     : https://prove2.me/submissions/e191a81d-324e-4fc9-bd97-b472ad26fa9c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

/-- Finite nested absolute energy gives product-measure L¹ integrability. -/
theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (F : α × β → ℝ)
    (hF : Measurable F)
    (hE : (∫⁻ a, ∫⁻ b, ENNReal.ofReal (|F (a,b)|) ∂ν ∂μ) < ⊤) :
    Integrable F (μ.prod ν) := by
  refine ⟨hF.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_norm]
  have hMf : Measurable (fun q : α × β => ENNReal.ofReal (‖F q‖)) :=
    ENNReal.measurable_ofReal.comp hF.norm
  rw [lintegral_prod _ hMf.aemeasurable]
  simpa only [Real.norm_eq_abs] using hE
