-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a96_original_fullcell_clipped_small_gaussian_source_positive_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T08:38:16.286205+00:00
-- url     : https://prove2.me/submissions/686a6484-b5a9-4c47-893d-353256158113

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ga_a63_original_stopped_positive_compact_safe_source_endpoint
import Theorems.Thm_AvramDividend_Classical_avram_ga_a71_original_gaussian_fullcell_clipped_spatial_endpoint_eq_source
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Every original physically complete pre-stop Gaussian cell with a small actual raw source increment has its genuine clipped spatial Taylor endpoint in a positive compact band. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j n m : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ i : ℕ,
      let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
      let s : ℝ≥0 := (i : ℝ≥0) * Δ
      let v : ℕ → ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (ρ ω)
      s < ρ ω → s + Δ ≤ ρ ω →
      |X.X (s + Δ) ω - X.X s ω| ≤
        (1 : ℝ) / (2 * ((j : ℝ) + 1)) →
      (1 : ℝ) / (2 * ((j : ℝ) + 1)) ≤
        x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ∧
      x + X.X (v (i + 1)) ω - rightLimit D (v i) ω ≤
        x + ((j : ℝ) + 1) +
          (1 : ℝ) / (2 * ((j : ℝ) + 1)) := by
  have hOriginal :=
    avram_ga_a63_original_stopped_positive_compact_safe_source_endpoint
      X x D hD ρ j hprefix
  filter_upwards [hOriginal] with ω hω
  intro i Δ s v hs hf hInc
  have hClocks :=
    avram_ga_a71_original_gaussian_fullcell_clipped_spatial_endpoint_eq_source
      X x D ω n m i (ρ ω) hf
  have hEndpoint := hClocks.2.2
  rw [hEndpoint]
  exact hω _ _ hs hInc
