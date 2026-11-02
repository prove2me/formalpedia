-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_bounded_predictable_weight_generator_negative_mark_L1_tail
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T17:51:31.020751+00:00
-- url     : https://prove2.me/submissions/0b011c65-8ebb-4e99-827d-c47aaadea15b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_negative_C2_generator_signed_drift_L1_tendsto_zero

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A predictable discount bounded by one contracts the actual physical
original-source nonlinear generator L1 small-mark drift tail. -/
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
    (T : ℝ≥0)
    (B : ℕ → Set ℝ)
    (hBm : ∀ n, MeasurableSet (B n))
    (hBneg : ∀ n, B n ⊆ Iio (0 : ℝ))
    (hBanti : Antitone B) (hBempty : (⋂ n, B n) = ∅)
    (ρ : ℝ≥0 × Ω → ℝ)
    (hρm : Measurable[𝓕.rightCont.predictable] ρ)
    (hρ : ∀ p, 0 ≤ ρ p ∧ ρ p ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖ρ p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
      atTop (𝓝 0) := by
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
    (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  let physical : Measure (ℝ≥0 × Ω) :=
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P
  change Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖ρ p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂physical)
    atTop (𝓝 0)
  have hTail : Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ‖∫ z in B n, JG (p,z) ∂X.ν‖ₑ ∂physical)
      atTop (𝓝 0) := by
    simpa only [physical, JG, Y] using
      (avram_wave5_03b_actual_finite_horizon_negative_C2_generator_signed_drift_L1_tendsto_zero
        X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv
        T B hBm hBneg hBanti hBempty)
  have hWeight (p : ℝ≥0 × Ω) : ‖ρ p‖ₑ ≤ (1 : ℝ≥0∞) := by
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (hρ p).1]
    calc
      ENNReal.ofReal (ρ p) ≤ ENNReal.ofReal (1 : ℝ) :=
        ENNReal.ofReal_le_ofReal (hρ p).2
      _ = 1 := by norm_num
  have hBound (n : ℕ) :
      (∫⁻ p : ℝ≥0 × Ω,
        ‖ρ p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ∂physical) ≤
      (∫⁻ p : ℝ≥0 × Ω,
        ‖∫ z in B n, JG (p,z) ∂X.ν‖ₑ ∂physical) := by
    apply lintegral_mono
    intro p
    change ‖ρ p * (∫ z in B n, JG (p,z) ∂X.ν)‖ₑ ≤
      ‖∫ z in B n, JG (p,z) ∂X.ν‖ₑ
    let V : ℝ := ∫ z in B n, JG (p,z) ∂X.ν
    change ‖ρ p * V‖ₑ ≤ ‖V‖ₑ
    simp only [Real.enorm_eq_ofReal_abs, abs_mul,
      abs_of_nonneg (hρ p).1]
    apply ENNReal.ofReal_le_ofReal
    have hsmall : 0 ≤ (1 - ρ p) * |V| :=
      mul_nonneg (sub_nonneg.mpr (hρ p).2) (abs_nonneg V)
    nlinarith
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le
    tendsto_const_nhds hTail (fun _ => bot_le) hBound
