-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_original_stopped_compact_full_generator_true_physical_predictable_clock_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T15:40:19.091646+00:00
-- url     : https://prove2.me/submissions/aa5da8e6-b1c1-4d9f-9823-88cd2792beb9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_controlled_compact_gaussian_generator_drift_L1_predictable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03_original_controlled_compact_linear_generator_residual_L1_predictable
import Theorems.Thm_AvramDividend_Classical_ruinTime_stopping_rightCont_filtration
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_inclusiveSurvival_stronglyPredictable

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

/-- The same finite predictable clock is the true physical time×P restriction,
and integrates all three stopped source Lévy generator drift components. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (q : ℝ) (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let ρ : ℝ≥0 × Ω → ℝ := fun p =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
    let G : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
      else 0
    let L : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc (u + δ) v then X.c * deriv w (Y p) - q * w (Y p)
      else 0
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ A : Set (ℝ≥0 × Ω),
        MeasurableSet[𝓕.rightCont.predictable] A →
          μ A = ((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
      Integrable (fun p : ℝ≥0 × Ω =>
        (ρ p * G p + ρ p * L p) +
          (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν)) μ := by
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let ρ : ℝ≥0 × Ω → ℝ := fun p =>
    if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then 1 else 0
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc (u + δ) v then X.σ ^ 2 / 2 * iteratedDeriv 2 w (Y p)
    else 0
  let L : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc (u + δ) v then X.c * deriv w (Y p) - q * w (Y p)
    else 0
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    ρ p.1 * (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  change ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
    μ Set.univ < ⊤ ∧
    (∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
        μ A = ((((volume : Measure ℝ).restrict
          (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A) ∧
    Integrable (fun p : ℝ≥0 × Ω =>
      (ρ p * G p + ρ p * L p) +
        (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν)) μ
  obtain ⟨μ, hμfinite, hμsets, hμlin⟩ :=
    avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
      X T
  refine ⟨μ, hμfinite, hμsets, ?_⟩
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  have hG : Integrable G μ := by
    simpa only [G, Y] using
      avram_wave5_03_original_controlled_compact_gaussian_generator_drift_L1_predictable
        X x D hD w 0 C (u + δ) v hw (by linarith) huv hv μ hμfinite
  have hL : Integrable L μ := by
    simpa only [L, Y] using
      avram_wave5_03_original_controlled_compact_linear_generator_residual_L1_predictable
        X x D hD w 0 C (u + δ) v hw (by linarith) huv hv q μ hμfinite
  have hJ : Integrable
      (fun p : ℝ≥0 × Ω => ∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) μ := by
    simpa only [JG, Y, ρ] using
      avram_wave5_03_original_signed_jump_drift_L1_on_true_predictable_clock
        X x D hD w C u v δ hw hw_cont hw_neg
          hu hδ hδone huv hv T μ hμlin
  have hStop := ruinTime_stopping_rightCont_filtration X x D hD
  have hSurvive := avram_wave3_04_inclusiveSurvival_stronglyPredictable
    (ruinTime X x D) hStop
  change StronglyMeasurable[𝓕.rightCont.predictable]
    (fun p : ℝ≥0 × Ω =>
      if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0)
      at hSurvive
  have hρmeas : Measurable ρ := hSurvive.measurable
  have hρbound : ∀ p : ℝ≥0 × Ω, ‖ρ p‖ ≤ (1 : ℝ) := by
    intro p
    by_cases h : (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2
    · simp [ρ, h]
    · simp [ρ, h]
  have hρae : ∀ᵐ p ∂μ, ‖ρ p‖ ≤ (1 : ℝ) :=
    Filter.Eventually.of_forall hρbound
  have hGI : Integrable (fun p => ρ p * G p) μ :=
    hG.bdd_mul hρmeas.aestronglyMeasurable hρae
  have hLI : Integrable (fun p => ρ p * L p) μ :=
    hL.bdd_mul hρmeas.aestronglyMeasurable hρae
  exact (hGI.add hLI).add hJ
