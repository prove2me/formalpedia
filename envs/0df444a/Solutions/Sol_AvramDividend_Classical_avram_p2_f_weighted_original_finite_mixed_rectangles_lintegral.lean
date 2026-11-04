-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_finite_mixed_rectangles_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:27:31.601204+00:00
-- url     : https://prove2.me/submissions/6ac1b84b-02a8-4446-9ad0-8b7c7ef1e426

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Tonelli linearity for a genuine original Lévy marked jump count
over finitely many differently timed and marked cells with separate weights. -/
theorem solution
    {ι Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (S : Finset ι) (s T : ι → ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i ∈ S, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable (H i)) :
    (∫⁻ ω, (∑ i ∈ S, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ (B i))) ∂P) =
    ∑ i ∈ S, (∫⁻ ω, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ (B i)) ∂P) := by
  exact MeasureTheory.lintegral_finset_sum S
    (fun i hi => (hH i hi).mul
      (avram_p2_f_weighted_original_intrinsic_rectangle_measurable
        X (s i) (T i) (B i) (hB i hi)))
