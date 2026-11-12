-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:55:27.207195+00:00
-- url     : https://prove2.me/submissions/e35e3282-fa54-42c8-917d-fc5ebc27af21

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger20_original_strict_prefix_postpayment_floor
import Theorems.Thm_AvramDividend_Classical_avram_gledger73_original_strict_prefix_postpayment_ceiling
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤
        x + X.X t ω - rightLimit D t ω ∧
      x + X.X t ω - rightLimit D t ω ≤
        x + ((j : ℝ) + 1) := by
  filter_upwards [hprefix] with ω hp
  intro t ht
  exact ⟨
    avram_gledger20_original_strict_prefix_postpayment_floor X x D hD ω
      (ρ ω) _ (fun s hs hsρ => (hp s hs hsρ).1) t ht,
    avram_gledger73_original_strict_prefix_postpayment_ceiling X x D hD ω
      (ρ ω) _ (fun s hs hsρ => (hp s hs hsρ).2) t ht⟩
