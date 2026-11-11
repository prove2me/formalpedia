-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin31_original_double_lintegral_to_product_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T18:05:55.206497+00:00
-- url     : https://prove2.me/submissions/83f697fd-2e1e-4467-8861-d9a2ed0dc327

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite ν]
    (H : α × β → ℝ)
    (hHm : AEStronglyMeasurable H (μ.prod ν))
    (hL1 : (∫⁻ a, ∫⁻ b, ENNReal.ofReal (|H (a,b)|) ∂ν ∂μ) < ⊤) :
    Integrable H (μ.prod ν) := by
  have hnorm : AEStronglyMeasurable (fun p => |H p|) (μ.prod ν) := by
    simpa only [Real.norm_eq_abs] using hHm.norm
  have hof : AEMeasurable (fun p => ENNReal.ofReal (|H p|)) (μ.prod ν) :=
    ENNReal.measurable_ofReal.comp_aemeasurable hnorm.aemeasurable
  have heq :
      (∫⁻ a, ∫⁻ b, ENNReal.ofReal (|H (a,b)|) ∂ν ∂μ) =
        ∫⁻ p, ENNReal.ofReal (|H p|) ∂(μ.prod ν) := by
    exact lintegral_lintegral hof
  have hprod : (∫⁻ p, ENNReal.ofReal (|H p|) ∂(μ.prod ν)) < ⊤ :=
    heq ▸ hL1
  have hnonneg : ∀ᵐ p ∂(μ.prod ν), 0 ≤ |H p| :=
    Filter.Eventually.of_forall (fun p => abs_nonneg (H p))
  have hi : Integrable (fun p => |H p|) (μ.prod ν) :=
    (lintegral_ofReal_ne_top_iff_integrable hnorm hnonneg).mp
      (ne_of_lt hprod)
  exact (integrable_norm_iff hHm).mp (by
    simpa only [Real.norm_eq_abs] using hi)
