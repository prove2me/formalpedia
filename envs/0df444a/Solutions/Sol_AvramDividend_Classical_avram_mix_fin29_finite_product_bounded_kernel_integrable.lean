-- Prove2me | solution 1 for AvramDividend.Classical.avram_mix_fin29_finite_product_bounded_kernel_integrable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:34:47.957632+00:00
-- url     : https://prove2.me/submissions/02f60194-8064-41f3-bb8a-e36667c484bb

import Mathlib.MeasureTheory.Integral.IntegrableOn
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (hμ : μ Set.univ < ∞) (hν : ν Set.univ < ∞)
    (H : α × β → ℝ)
    (hHm : AEStronglyMeasurable H (μ.prod ν))
    (K : ℝ) (hK0 : 0 ≤ K)
    (hK : ∀ p, |H p| ≤ K) :
    Integrable H (μ.prod ν) := by
  letI : IsFiniteMeasure μ := ⟨hμ⟩
  letI : IsFiniteMeasure ν := ⟨hν⟩
  apply Integrable.of_bound hHm K
  filter_upwards [] with p
  simpa only [Real.norm_eq_abs] using hK p
