-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_countable_mixed_rectangles_lintegral
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:24:46.080751+00:00
-- url     : https://prove2.me/submissions/b413ac9f-0e1e-4e6e-b7d1-200892b8052d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_original_intrinsic_rectangle_measurable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Countable Tonelli interchange for genuine original Lévy marked
rectangles with separately varying deterministic times, marks and weights. -/
theorem solution
    {ι Ω : Type*} [Countable ι] [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ι → ℝ≥0) (B : ι → Set ℝ)
    (hB : ∀ i, MeasurableSet (B i))
    (H : ι → Ω → ℝ≥0∞)
    (hH : ∀ i, Measurable (H i)) :
    (∫⁻ ω, (∑' i : ι, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ (B i))) ∂P) =
    ∑' i : ι, (∫⁻ ω, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (s i + T i) ×ˢ (B i)) ∂P) := by
  exact MeasureTheory.lintegral_tsum
    (fun i => ((hH i).mul
      (avram_p2_f_weighted_original_intrinsic_rectangle_measurable
        X (s i) (T i) (B i) (hB i))).aemeasurable)
