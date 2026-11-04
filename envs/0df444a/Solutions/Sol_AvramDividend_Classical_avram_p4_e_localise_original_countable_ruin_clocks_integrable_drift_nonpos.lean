-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_countable_ruin_clocks_integrable_drift_nonpos
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:28:40.232278+00:00
-- url     : https://prove2.me/submissions/50ba56e7-ce76-476d-b689-f8fd15e1c0cf

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_true_stopped_integrable_generator_density_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Finite original source stopped drifts are jointly nonpositive for all horizons. -/
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
    (hF : ∀ k (y : ℝ), 0 < y → y < c → F k y ≤ 0)
    (hIntegrable : ∀ k ω, Integrable
      (fun t : ℝ≥0 => if 0 < t ∧ (t : ℝ≥0∞) < τ k ω
        then F k (riskProcess X x D t ω) else 0) (μ k)) :
    ∀ᵐ ω ∂P, ∀ k,
      (∫ t : ℝ≥0, if 0 < t ∧ (t : ℝ≥0∞) < τ k ω
        then F k (riskProcess X x D t ω) else 0 ∂(μ k)) ≤ 0 := by
  apply ae_all_iff.mpr
  intro k
  letI : SFinite (μ k) := hμ k
  exact avram_p4_e_localise_original_true_stopped_integrable_generator_density_nonpos
    X hBV x c D hD hDiv hCap (τ k) (hτ k) (μ k) (F k) (hF k)
    (hIntegrable k)
