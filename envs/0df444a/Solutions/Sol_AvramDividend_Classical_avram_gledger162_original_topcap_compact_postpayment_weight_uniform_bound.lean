-- Prove2me | solution 1 for AvramDividend.Classical.avram_gledger162_original_topcap_compact_postpayment_weight_uniform_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:23:05.697678+00:00
-- url     : https://prove2.me/submissions/f2e4baa0-aaa1-4234-ade2-7226a77425ba

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hTopCap : C = ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (hx : 0 < x)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ρ : Ω → ℝ≥0) (j : ℕ)
    (hprefix : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, 0 < t → t < ρ ω →
      (1 : ℝ) / ((j : ℝ) + 1) ≤ riskProcess X x D t ω ∧
      riskProcess X x D t ω ≤ x + ((j : ℝ) + 1)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ᵐ ω ∂P, ∀ t : ℝ≥0, t < ρ ω →
      |w (x + X.X t ω - rightLimit D t ω)| ≤ K := by
  let a : ℝ := 1 / ((j : ℝ) + 1)
  let b : ℝ := x + ((j : ℝ) + 1)
  have ha : 0 < a := by dsimp [a]; positivity
  have hsub : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C} := by
    intro y hy
    exact ⟨lt_of_lt_of_le ha hy.1, by simp [hTopCap]⟩
  have hc : ContinuousOn w (Icc a b) := hw_smooth.continuousOn.mono hsub
  obtain ⟨K, hK⟩ := isCompact_Icc.exists_bound_of_continuousOn hc
  refine ⟨max K 0, le_max_right _ _, ?_⟩
  filter_upwards [avram_gledger137_original_gaussian_source_postpayment_compact_prefix_band
    X x D hD ρ j hprefix] with ω hω
  intro t ht
  have hy : x + X.X t ω - rightLimit D t ω ∈ Icc a b := hω t ht
  have he := hK _ hy
  simpa only [Real.norm_eq_abs] using he.trans (le_max_left K 0)
