-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_full_negative_C2_generator_pathwise_time_L1_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T13:25:04.101066+00:00
-- url     : https://prove2.me/submissions/5c75ab1d-d1e6-4277-802b-696867f74359

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_full_negative_C2_generator_band_to_full_uniform

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- For the literal original controlled Lévy reserve, every sample path has
vanishing time-integrated nonlinear source-generator truncation error against
any finite deterministic time measure; no Poisson copy or martingale claim. -/
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
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (μ : Measure ℝ≥0) (hμ : μ Set.univ ≠ ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    ∀ ω : Ω, Tendsto
      (fun n : ℕ => ∫⁻ q : ℝ≥0,
        ‖(∫ z in Iio (0 : ℝ), JG ((q,ω),z) ∂X.ν) -
          (∫ z in Iio (0 : ℝ) \ B n, JG ((q,ω),z) ∂X.ν)‖ₑ ∂μ)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
    (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  change ∀ ω : Ω, Tendsto
    (fun n : ℕ => ∫⁻ q : ℝ≥0,
      ‖(∫ z in Iio (0 : ℝ), JG ((q,ω),z) ∂X.ν) -
        (∫ z in Iio (0 : ℝ) \ B n, JG ((q,ω),z) ∂X.ν)‖ₑ ∂μ)
    atTop (𝓝 (0 : ℝ≥0∞))
  obtain ⟨err, herr, hUniform⟩ :=
    avram_wave5_03b_actual_full_negative_C2_generator_band_to_full_uniform
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv B hBm hBneg hBanti hBempty
  intro ω
  have hbound (n : ℕ) :
      (∫⁻ q : ℝ≥0,
        ‖(∫ z in Iio (0 : ℝ), JG ((q,ω),z) ∂X.ν) -
          (∫ z in Iio (0 : ℝ) \ B n, JG ((q,ω),z) ∂X.ν)‖ₑ ∂μ) ≤
          μ Set.univ * err n := by
    calc
      _ ≤ ∫⁻ q : ℝ≥0, err n ∂μ := by
        apply lintegral_mono
        intro q
        exact hUniform n (q,ω)
      _ = μ Set.univ * err n := by
        rw [MeasureTheory.lintegral_const]
        exact mul_comm _ _
  have hmul : Tendsto (fun n : ℕ => μ Set.univ * err n)
      atTop (𝓝 (0 : ℝ≥0∞)) := by
    simpa using
      (ENNReal.Tendsto.const_mul (a := μ Set.univ) herr (Or.inr hμ))
  exact Filter.Tendsto.squeeze
    tendsto_const_nhds hmul (fun n => bot_le) hbound
