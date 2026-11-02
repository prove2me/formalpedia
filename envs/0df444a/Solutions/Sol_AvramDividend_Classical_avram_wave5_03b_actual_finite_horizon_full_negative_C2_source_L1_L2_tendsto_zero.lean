-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_L1_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:25:44.480856+00:00
-- url     : https://prove2.me/submissions/5497233a-313f-416d-8084-6bebed5a5648

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_L1_L2_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Genuine finite-horizon time×original P realisation of the full negative
source stopped Taylor L1/L2 predictable tail limits for all general C² w. -/
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
    (T : ℝ≥0) :
    ∃ μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable),
      μ Set.univ < ⊤ ∧
      (∀ f : (ℝ≥0 × Ω) → ℝ≥0∞,
        Measurable[𝓕.rightCont.predictable] f →
        (∫⁻ p, f p ∂μ) =
          (∫⁻ p, f p ∂((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P))) ∧
      let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
        (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
      let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        (if Y p.1 ∈ Icc (u + δ) v then
          w (Y p.1 + p.2) - w (Y p.1) else 0) -
        (if -1 < p.2 then
          p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
          else 0)
      let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
        (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
      ∀ (B : ℕ → Set ℝ)
        (hBm : ∀ n, MeasurableSet (B n))
        (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
        (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
        Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ)
          atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ)
          atTop (𝓝 0) := by
  obtain ⟨μ, hμ, _hset, hprod⟩ :=
    avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
      X T
  refine ⟨μ, hμ, hprod, ?_⟩
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  change ∀ (B : ℕ → Set ℝ)
        (hBm : ∀ n, MeasurableSet (B n))
        (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
        (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅),
        Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ)
          atTop (𝓝 0) ∧
        Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
          ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ)
          atTop (𝓝 0)
  intro B hBm hBneg hBanti hBempty
  exact avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_L1_L2_tendsto_zero
    X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
    μ hμ B hBm hBneg hBanti hBempty
