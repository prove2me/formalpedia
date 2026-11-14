-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a63_original_stopped_positive_compact_safe_source_endpoint
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T07:41:08.108285+00:00
-- url     : https://prove2.me/submissions/f08a3b0b-601b-4fdd-be98-acc7f4d75c78

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
import Theorems.Thm_AvramDividend_Classical_avram_ga_a47_original_small_source_increment_enlarged_compact_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- On the genuine stopped Gaussian compact prepayment reserve prefix, every small-increment source Taylor endpoint stays uniformly in a positive larger compact band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ s t : ℝ≥0, s < ρ ω →
      |X.X t ω - X.X s ω| ≤ (1 : ℝ) / (2 * ((j : ℝ) + 1)) →
      (1 : ℝ) / (2 * ((j : ℝ) + 1)) ≤
        x + X.X t ω - rightLimit D s ω ∧
      x + X.X t ω - rightLimit D s ω ≤
        x + ((j : ℝ) + 1) + (1 : ℝ) / (2 * ((j : ℝ) + 1)) := by
  have hBand :=
    avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
      X x D hD ρ j hprefix
  filter_upwards [hBand] with ω hω
  intro s t hs hInc
  have hpos : (0 : ℝ) < 1 / ((j : ℝ) + 1) := by positivity
  have hδpos : (0 : ℝ) ≤ 1 / (2 * ((j : ℝ) + 1)) := by positivity
  have hδeq : (1 : ℝ) / (2 * ((j : ℝ) + 1)) =
      (1 / ((j : ℝ) + 1)) / 2 := by
    have hden : (j : ℝ) + 1 ≠ 0 := ne_of_gt (by positivity)
    field_simp [hden] <;> ring
  have h := avram_ga_a47_original_small_source_increment_enlarged_compact_band
    X x D ω s t
    (1 / ((j : ℝ) + 1)) (x + ((j : ℝ) + 1))
    (1 / (2 * ((j : ℝ) + 1)))
    hpos hδpos hδeq.le (hω s hs) hInc
  simpa only [hδeq] using h
