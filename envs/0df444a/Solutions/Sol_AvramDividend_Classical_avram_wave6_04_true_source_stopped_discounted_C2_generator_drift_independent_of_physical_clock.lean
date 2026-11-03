-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_true_source_stopped_discounted_C2_generator_drift_independent_of_physical_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T08:45:11.997909+00:00
-- url     : https://prove2.me/submissions/72edd2ef-e292-43a2-8bf2-d030a5ed8022

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_04_true_source_physical_predictable_clock_unique

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The genuine source nonlinear stopped discounted generator drift depends
only on the canonical finite physical clock, not its measure presentation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (u v δ : ℝ) (T : ℝ≥0)
    (μ₁ μ₂ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ₁ : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ₁ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (hμ₂ : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ₂ A =
        ((((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map
          Real.toNNReal).prod P) A)
    (τ : Ω → ℝ≥0∞) (hτ : IsStoppingTime 𝓕.rightCont τ)
    (q : ℝ) (hq : 0 ≤ q) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    let a : ℝ≥0 × Ω → ℝ := fun p =>
      (if p.1 ≤ T then Real.exp (-(q * (p.1 : ℝ))) else 0) *
      (if (p.1 : ℝ≥0∞) ≤ τ p.2 then (1 : ℝ) else 0)
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω,
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν) ∂μ₁) =
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
      ∫ p : ℝ≥0 × Ω,
        a p * (∫ z in Iio (0 : ℝ), JG (p, z) ∂X.ν) ∂μ₂) := by
  intro Y JG a
  have hμ : μ₁ = μ₂ :=
    avram_wave6_04_true_source_physical_predictable_clock_unique
      𝓕 T μ₁ μ₂ hμ₁ hμ₂
  rw [hμ]
