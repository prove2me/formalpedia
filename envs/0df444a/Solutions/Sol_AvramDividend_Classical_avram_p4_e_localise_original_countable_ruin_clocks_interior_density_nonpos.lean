-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_countable_ruin_clocks_interior_density_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:28:44.208201+00:00
-- url     : https://prove2.me/submissions/b96df17d-373c-4058-a5f2-f8287e41a9d8

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_stopped_interior_residual_density_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- The genuine source occupation sign holds on one conull set for every localiser. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x c : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsAdmissibleLe X x (ENNReal.ofReal c) D)
    (hDiv : IsDividendStrategy 𝓕 D)
    (hCap : ∀ ω (s : ℝ≥0),
      (s : ℝ≥0∞) < ruinTime X x D ω → riskProcess X x D s ω ≤ c)
    (τ : ℕ → Ω → ℝ≥0∞)
    (hτ : ∀ k ω, τ k ω ≤ ruinTime X x D ω)
    (μ : ℕ → Measure ℝ≥0) (hμ : ∀ k, SFinite (μ k))
    (F : ℕ → ℝ → ℝ)
    (hF : ∀ k (y : ℝ), 0 < y → y < c → F k y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ k, ∀ᵐ t : ℝ≥0 ∂(μ k),
      0 < t → (t : ℝ≥0∞) < τ k ω →
      F k (riskProcess X x D t ω) ≤ 0 := by
  apply ae_all_iff.mpr
  intro k
  letI : SFinite (μ k) := hμ k
  exact avram_p4_e_localise_original_true_stopped_interior_residual_density_nonpos
    X hBV x c D hD hDiv hCap (τ k) (hτ k) (μ k) (F k) (hF k)
