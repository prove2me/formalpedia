-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn28_original_stopped_signed_HJB_source_clock_budget
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T00:22:18.694512+00:00
-- url     : https://prove2.me/submissions/eb9fedd0-f27d-45ad-8aca-be4f3cb084d2

import Mathlib.Probability.Martingale.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn25_original_stopped_martingale_source_plus_negative_drift
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original stopped martingale and actual localised HJB generator drift have signed finite-grid expectation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (C : ℝ≥0∞) (hC : 0 < C)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (U : ℝ≥0 × Ω → ℝ) (E : Set (ℝ≥0 × Ω))
    (hInterior : ∀ p ∈ E, 0 < U p ∧ ENNReal.ofReal (U p) < C)
    (Y : ℝ≥0 → Ω → ℝ)
    (hMart : Martingale Y 𝓕.rightCont P)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (μ : Measure ℝ≥0)
    (hBI : ∀ i, Integrable (fun ω =>
      ∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ) P) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range m,
        if (u i : WithTop ℝ≥0) < τ ω then
          (Y (u (i + 1)) ω - Y (u i) ω) +
          (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ)
        else 0) P ∧
    (∫ ω, ∑ i ∈ Finset.range m,
      (if (u i : WithTop ℝ≥0) < τ ω then
        (Y (u (i + 1)) ω - Y (u i) ω) +
        (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ)
       else 0) ∂P) ≤ 0 := by
  let B : ℕ → Ω → ℝ := fun i ω =>
    ∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ
  have hDrift (i : ℕ) (ω : Ω) : B i ω ≤ 0 := by
    dsimp [B]
    apply integral_nonpos
    intro t
    exact avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
      X q hq w C hC hw_gen U E hInterior (t, ω)
  exact avram_bv_env3_turn25_original_stopped_martingale_source_plus_negative_drift
    X Y hMart τ hStop u hu m B hBI hDrift
