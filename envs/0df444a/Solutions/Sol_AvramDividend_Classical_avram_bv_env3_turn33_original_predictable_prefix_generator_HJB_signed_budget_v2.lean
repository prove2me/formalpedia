-- Prove2me | solution 1 for AvramDividend.Classical.avram_bv_env3_turn33_original_predictable_prefix_generator_HJB_signed_budget_v2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T06:31:00.97997+00:00
-- url     : https://prove2.me/submissions/0109b93c-171e-4dc7-8edc-2ebcf3ca24cc

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn26_original_localised_HJB_signed_density_nonpos
import Theorems.Thm_AvramDividend_Classical_avram_bv_env3_turn29_original_source_predictable_bounded_prefix_signed_budget
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual localised original-generator HJB drift has nonpositive expectation
    together with a bounded predictable prefix of physical martingale increments. -/
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
    (Y : ℝ≥0 → Ω → ℝ) (hMart : Martingale Y 𝓕.rightCont P)
    (u : ℕ → ℝ≥0) (hu : Monotone u) (m : ℕ)
    (k : Ω → ℕ) (hk : Measurable k) (hkBound : ∀ ω, k ω ≤ m)
    (hPredictable : ∀ i : ℕ, MeasurableSet[𝓕.rightCont (u i)]
      {ω : Ω | i < k ω})
    (μ : Measure ℝ≥0)
    (hBI : ∀ i : ℕ, Integrable (fun ω =>
      ∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ) P) :
    Integrable (fun ω =>
      ∑ i ∈ Finset.range (k ω),
        ((Y (u (i + 1)) ω - Y (u i) ω) +
        (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
              Real.exp (-(q * (t : ℝ))) *
                (X.generator w (U (t, ω)) - q * w (U (t, ω)))
             else 0) ∂μ))) P ∧
    (∫ ω, ∑ i ∈ Finset.range (k ω),
      ((Y (u (i + 1)) ω - Y (u i) ω) +
      (∫ t in Ioc (u i) (u (i + 1)), (if (t, ω) ∈ E then
            Real.exp (-(q * (t : ℝ))) *
              (X.generator w (U (t, ω)) - q * w (U (t, ω)))
           else 0) ∂μ)) ∂P) ≤ 0 := by
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
  exact avram_bv_env3_turn29_original_source_predictable_bounded_prefix_signed_budget
    X Y hMart u hu m k hk hkBound hPredictable B hBI hDrift
