-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_physical_L1_L2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T10:47:28.264252+00:00
-- url     : https://prove2.me/submissions/75439980-6a35-4217-9e0f-f67e20bd9ee5

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_L1_L2_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Ordinary small-negative-mark L1/L2 source intensity convergence directly under
the physical original P times bounded Lebesgue time; no auxiliary μ remains. -/
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
      ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂
      (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)
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
  let physical : Measure (ℝ≥0 × Ω) :=
    (((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal).prod P
  change Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν ∂physical)
      atTop (𝓝 0) ∧
    Tendsto (fun n : ℕ => ∫⁻ p : ℝ≥0 × Ω,
      ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν ∂physical)
      atTop (𝓝 0)
  obtain ⟨μ, hμ, hprod, hTail⟩ :=
    avram_wave5_03b_actual_finite_horizon_full_negative_C2_source_L1_L2_tendsto_zero
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv T
  have hMeas :=
    (avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv μ hμ).1
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  have hRestrict (n : ℕ) :
      (X.ν.restrict (Iio (0 : ℝ))).restrict (B n) =
        X.ν.restrict (B n) := by
    rw [Measure.restrict_restrict (hBm n)]
    rw [Set.inter_eq_left.mpr (hBneg n)]
  let F1 (n : ℕ) (p : ℝ≥0 × Ω) : ℝ≥0∞ :=
    ∫⁻ z in B n, ENNReal.ofReal (|HS (p,z)|) ∂X.ν
  let F2 (n : ℕ) (p : ℝ≥0 × Ω) : ℝ≥0∞ :=
    ∫⁻ z in B n, ENNReal.ofReal ((HS (p,z)) ^ 2) ∂X.ν
  have hm1 (n : ℕ) :
      Measurable[𝓕.rightCont.predictable] (F1 n) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    letI : SFinite (X.ν.restrict (B n)) := by
      rw [← hRestrict n]
      infer_instance
    have hk : Measurable
        (fun p : ((ℝ≥0 × Ω) × ℝ) => ENNReal.ofReal (|HS p|)) :=
      ENNReal.measurable_ofReal.comp hMeas.abs
    exact Measurable.lintegral_prod_right hk
  have hm2 (n : ℕ) :
      Measurable[𝓕.rightCont.predictable] (F2 n) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    letI : SFinite (X.ν.restrict (B n)) := by
      rw [← hRestrict n]
      infer_instance
    have hk : Measurable
        (fun p : ((ℝ≥0 × Ω) × ℝ) => ENNReal.ofReal ((HS p) ^ 2)) :=
      ENNReal.measurable_ofReal.comp (hMeas.pow_const 2)
    exact Measurable.lintegral_prod_right hk
  have heq1 : (fun n : ℕ => ∫⁻ p, F1 n p ∂physical) =
      (fun n : ℕ => ∫⁻ p, F1 n p ∂μ) := by
    funext n
    exact (hprod (F1 n) (hm1 n)).symm
  have heq2 : (fun n : ℕ => ∫⁻ p, F2 n p ∂physical) =
      (fun n : ℕ => ∫⁻ p, F2 n p ∂μ) := by
    funext n
    exact (hprod (F2 n) (hm2 n)).symm
  obtain ⟨hL1, hL2⟩ := hTail B hBm hBneg hBanti hBempty
  constructor
  · change Tendsto (fun n : ℕ => ∫⁻ p, F1 n p ∂physical) atTop (𝓝 0)
    rw [heq1]
    exact hL1
  · change Tendsto (fun n : ℕ => ∫⁻ p, F2 n p ∂physical) atTop (𝓝 0)
    rw [heq2]
    exact hL2
