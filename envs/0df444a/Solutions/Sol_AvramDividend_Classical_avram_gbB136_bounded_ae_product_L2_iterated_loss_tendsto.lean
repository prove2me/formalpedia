-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB136_bounded_ae_product_L2_iterated_loss_tendsto
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T08:42:35.430603+00:00
-- url     : https://prove2.me/submissions/8e5f9519-fb3d-4a15-8c12-09bfc5f26ce9

import Mathlib.MeasureTheory.Integral.Prod
import Theorems.Thm_AvramDividend_Classical_avram_gbB118_bounded_ae_L2_loss_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_gbB129_bounded_measurable_squared_difference_integrable
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (f : ℕ → α × β → ℝ) (g : α × β → ℝ)
    (hf : ∀ m, Measurable (f m)) (hg : Measurable g)
    (B : ℝ) (hB : 0 ≤ B)
    (hfb : ∀ m z, |f m z| ≤ B) (hgb : ∀ z, |g z| ≤ B)
    (hae : ∀ᵐ z ∂(μ.prod ν), Tendsto (fun m => f m z) atTop (𝓝 (g z))) :
    Tendsto (fun m : ℕ =>
      ∫ a, (∫ b, (f m (a, b) - g (a, b)) ^ 2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by
  have hprod :
      Tendsto (fun m => ∫ z, (f m z - g z) ^ 2 ∂(μ.prod ν))
        atTop (𝓝 (0 : ℝ)) :=
    AvramDividend.Classical.avram_gbB118_bounded_ae_L2_loss_tendsto
      (μ.prod ν) f g (fun m => (hf m).aestronglyMeasurable)
      hg.aestronglyMeasurable B hB
      (fun m => Filter.Eventually.of_forall (hfb m))
      (Filter.Eventually.of_forall hgb) hae
  have heq (m : ℕ) :
      (∫ z, (f m z - g z) ^ 2 ∂(μ.prod ν)) =
      ∫ a, (∫ b, (f m (a, b) - g (a, b)) ^ 2 ∂ν) ∂μ := by
    have hi :=
      AvramDividend.Classical.avram_gbB129_bounded_measurable_squared_difference_integrable
        (μ.prod ν) (f m) g (hf m) hg B hB (hfb m) hgb
    exact integral_prod (fun z => (f m z - g z) ^ 2) hi
  simpa only [heq] using hprod
