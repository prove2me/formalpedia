-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_bounded_predictable_weight_full_negative_C2_source_L1_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T19:24:57.006472+00:00
-- url     : https://prove2.me/submissions/2eb23ba7-7348-4dd2-bc50-5cd22ed9d309

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_L1_L2_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
/-- A predictable weight in [0,1] contracts the full negative
original-source stopped nonlinear Taylor L1 and L2 small-mark energies. -/
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
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (ρ : ℝ≥0 × Ω → ℝ)
    (hρm : Measurable[𝓕.rightCont.predictable] ρ)
    (hρ : ∀ p, 0 ≤ ρ p ∧ ρ p ≤ 1) :
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
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal (|ρ p * HS (p,z)|) ∂X.ν ∂μ)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((ρ p * HS (p,z)) ^ 2) ∂X.ν ∂μ)
      atTop (𝓝 0) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => (if Y p.1 ∈ Icc (u + δ) v then w (Y p.1 + p.2) - w (Y p.1) else 0) - (if -1 < p.2 then p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0) else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p => (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  change Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal (|ρ p * HS (p,z)|) ∂X.ν ∂μ)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((ρ p * HS (p,z)) ^ 2) ∂X.ν ∂μ)
      atTop (𝓝 0)
  have hTail :
      Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ)
        atTop (𝓝 0) ∧
      Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ)
        atTop (𝓝 0) := by
    simpa only [Y, H, HS] using
      (avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_L1_L2_tendsto_zero
        X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
        μ hμ B hBm hBneg hBanti hBempty)
  have hAbs (p : ℝ≥0 × Ω) (z : ℝ) :
      |ρ p * HS (p,z)| ≤ |HS (p,z)| := by
    rw [abs_mul, abs_of_nonneg (hρ p).1]
    calc
      ρ p * |HS (p,z)| ≤ 1 * |HS (p,z)| :=
        mul_le_mul_of_nonneg_right (hρ p).2 (abs_nonneg _)
      _ = _ := one_mul _
  have hSq (p : ℝ≥0 × Ω) (z : ℝ) :
      (ρ p * HS (p,z)) ^ 2 ≤ (HS (p,z)) ^ 2 := by
    have hρsq : (ρ p) ^ 2 ≤ (1 : ℝ) := by
      have haux : 0 ≤ ρ p * (1 - ρ p) :=
        mul_nonneg (hρ p).1 (sub_nonneg.mpr (hρ p).2)
      nlinarith
    calc
      (ρ p * HS (p,z)) ^ 2 = (ρ p) ^ 2 * (HS (p,z)) ^ 2 := by ring
      _ ≤ 1 * (HS (p,z)) ^ 2 :=
        mul_le_mul_of_nonneg_right hρsq (sq_nonneg _)
      _ = _ := one_mul _
  have hBound1 (n : ℕ) :
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|ρ p * HS (p,z)|) ∂X.ν ∂μ) ≤
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) := by
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro z
    exact ENNReal.ofReal_le_ofReal (hAbs p z)
  have hBound2 (n : ℕ) :
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((ρ p * HS (p,z)) ^ 2) ∂X.ν ∂μ) ≤
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) := by
    apply lintegral_mono
    intro p
    apply lintegral_mono
    intro z
    exact ENNReal.ofReal_le_ofReal (hSq p z)
  constructor
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hTail.1 (fun _ => bot_le) hBound1
  · exact tendsto_of_tendsto_of_tendsto_of_le_of_le
      tendsto_const_nhds hTail.2 (fun _ => bot_le) hBound2
