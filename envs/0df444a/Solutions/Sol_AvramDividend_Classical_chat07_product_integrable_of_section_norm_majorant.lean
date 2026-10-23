-- Prove2me | solution 1 for AvramDividend.Classical.chat07_product_integrable_of_section_norm_majorant
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T07:35:43.845868+00:00
-- url     : https://prove2.me/submissions/ba4640b4-5714-4ec3-9d7c-064e754f7db2

import Mathlib.MeasureTheory.Integral.Prod
import Mathlib.MeasureTheory.Function.L1Space.Integrable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory

-- An integrable scalar envelope on section norms yields product L1.
theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [SFinite μ] [SFinite ν]
    (K : α × β → ℝ) (g : β → ℝ)
    (hK : AEStronglyMeasurable K (μ.prod ν))
    (hsections : ∀ᵐ r ∂ν, Integrable (fun x : α => K (x,r)) μ)
    (hinner : AEStronglyMeasurable
      (fun r : β => ∫ x : α, ‖K (x,r)‖ ∂μ) ν)
    (hg : Integrable g ν)
    (hmajor : ∀ᵐ r ∂ν,
      (∫ x : α, ‖K (x,r)‖ ∂μ) ≤ g r) :
    Integrable K (μ.prod ν) := by
  apply (integrable_prod_iff' hK).2
  refine ⟨hsections, ?_⟩
  apply Integrable.mono_nonneg hg hinner
  · exact Filter.Eventually.of_forall
      (fun r => integral_nonneg (fun x => norm_nonneg (K (x,r))))
  · exact hmajor
