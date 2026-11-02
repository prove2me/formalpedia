-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_L1_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:20:27.191215+00:00
-- url     : https://prove2.me/submissions/84a107f9-c79a-4d7c-8ff8-9da4ca027aec

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_band_tail
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Ordinary convergence (not only infimum-zero) of the actual controlled
ruin-stopped nonlinear source jump absolute L1 and quadratic L2 tails over
arbitrary decreasing negative-mark bands. No stochastic isometry is asserted. -/
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
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅) :
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
      ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ)
      atTop (𝓝 0) := by
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
  change Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ)
      atTop (𝓝 0)
  have hL1 : (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ) = 0 :=
    avram_wave5_03b_actual_ruin_stopped_full_negative_C2_source_taylor_L1_band_tail
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
      μ hμ B hBm hBneg hBanti hBempty
  have hL2 : (⨅ n : ℕ, ∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ) = 0 :=
    avram_wave5_03b_actual_ruin_stopped_compensated_taylor_small_mark_L2_tail
      X x D hD w 0 C u v δ hw hw_cont hw_neg
      hu (by linarith) hv (le_of_lt hu)
      hδ hδone (le_of_lt huv) μ hμ B hBm hBneg hBanti hBempty
  let A1 (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂μ
  let A2 (n : ℕ) : ℝ≥0∞ :=
    ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂μ
  have hA1 : Antitone A1 := by
    intro i j hij
    apply lintegral_mono
    intro p
    exact lintegral_mono_set (hBanti hij)
  have hA2 : Antitone A2 := by
    intro i j hij
    apply lintegral_mono
    intro p
    exact lintegral_mono_set (hBanti hij)
  have hConv1 : Tendsto A1 atTop (𝓝 0) := by
    have h := tendsto_atTop_iInf hA1
    rw [hL1] at h
    exact h
  have hConv2 : Tendsto A2 atTop (𝓝 0) := by
    have h := tendsto_atTop_iInf hA2
    rw [hL2] at h
    exact h
  exact ⟨hConv1, hConv2⟩
