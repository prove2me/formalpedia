-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_e_localise_original_countable_atomless_predictable_finite_cap_HJB_ae
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:48:01.521935+00:00
-- url     : https://prove2.me/submissions/5700564c-5494-47a6-9c33-972ab05d2b4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_atomless_predictable_finite_cap_generator_HJB_ae
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- Original countable atomless localisation clocks have simultaneous predictable pre-event finite-cap HJB sign. -/
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
    (μ : ℕ → Measure ℝ≥0)
    (hμ : ∀ k, SFinite (μ k))
    (hAtomless : ∀ k, NullSingletonClass (μ k))
    (w : ℝ → ℝ) (q : ℝ)
    (hwGen : ∀ y : ℝ, 0 < y → y < c →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P, ∀ k, ∀ᵐ t : ℝ≥0 ∂μ k,
      0 < t → (t : ℝ≥0∞) < τ k ω →
      X.GeneratorIntegrable w (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t) ∧
      X.generator w (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t) -
        q * w (Function.leftLim
        (fun r : ℝ≥0 => x + X.X r ω - rightLimit D r ω) t) ≤ 0 := by
  apply ae_all_iff.mpr
  intro k
  letI : SFinite (μ k) := hμ k
  letI : NullSingletonClass (μ k) := hAtomless k
  exact avram_p4_e_localise_original_atomless_predictable_finite_cap_generator_HJB_ae
    X hBV x c D hD hDiv hCap (τ k) (hτ k) (μ k) w q hwGen
