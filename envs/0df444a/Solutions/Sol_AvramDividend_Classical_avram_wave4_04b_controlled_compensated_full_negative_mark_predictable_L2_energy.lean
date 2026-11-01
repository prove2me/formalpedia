-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_controlled_compensated_full_negative_mark_predictable_L2_energy
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T20:39:14.392945+00:00
-- url     : https://prove2.me/submissions/4888ca4f-8b61-444f-aeb1-567db3551c23

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal Classical
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0) -
      (if -1 < p.2 then
        p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
        else 0)
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  dsimp only
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let G : ℝ≥0 × Ω → ℝ := fun p =>
    if Y p ∈ Icc (u + δ) v then deriv w (Y p) else 0
  let J : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    J p - (if -1 < p.2 then p.2 * G p.1 else 0)
  change Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] H ∧
      (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  have hau' : a < u + δ := by linarith
  obtain ⟨K, hK, hpoint⟩ :=
    avram_wave4_04b_original_full_negative_mark_compensated_kernel_uniform_energy_envelope
      X w a b u v δ hw1 hw_cont hw_neg hau huv hvb hu0 hδ hδone hband
  have hGmeas : Measurable[𝓕.rightCont.predictable] G :=
    (avram_wave4_04b_controlled_prejump_gradient_compact_band_L2_energy
      X x D hD w a b (u + δ) v hw hau' hband hvb μ hμ).1
  have hJmeas : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] J :=
    (avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
      X x D hD w a b u v δ hw1 hw_cont hw_neg
      hau huv hvb hu0 hδ hδone hband μ hμ).1
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)
  have hGmark : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) => G p.1) :=
    hGmeas.comp measurable_fst
  have hsmall : MeasurableSet {p : ((ℝ≥0 × Ω) × ℝ) | -1 < p.2} :=
    measurableSet_Ioi.preimage measurable_snd
  have htrunc : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      if -1 < p.2 then p.2 * G p.1 else 0) :=
    (measurable_snd.mul hGmark).ite hsmall measurable_const
  have hHmeas : Measurable H := hJmeas.sub htrunc
  refine ⟨hHmeas, ?_⟩
  have hνmeas : Measurable (fun z : ℝ =>
      ENNReal.ofReal (min 1 (z ^ 2))) := by fun_prop
  have hM : ENNReal.ofReal K *
      (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) < ⊤ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top X.ν_integrable
  have hinner (p : ℝ≥0 × Ω) :
      (∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν) ≤
        ENNReal.ofReal K *
          (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) := by
    have hbound (z : ℝ) (hz : z ∈ Iio (0 : ℝ)) :
        ENNReal.ofReal ((H (p, z)) ^ 2) ≤
          ENNReal.ofReal K * ENNReal.ofReal (min 1 (z ^ 2)) := by
      by_cases hb : Y p ∈ Icc (u + δ) v
      · have hExpr : H (p, z) =
            w (Y p + z) - w (Y p) -
              (if -1 < z then z * deriv w (Y p) else 0) := by
          have hb' : u + δ ≤ Y p ∧ Y p ≤ v := hb
          simp [H, J, G, Set.mem_Icc, hb']
        rw [hExpr, ← ENNReal.ofReal_mul hK]
        exact ENNReal.ofReal_le_ofReal (hpoint (Y p) hb z hz)
      · have hExpr : H (p, z) = 0 := by
          have hb' : ¬ (u + δ ≤ Y p ∧ Y p ≤ v) := hb
          simp [H, J, G, Set.mem_Icc, hb']
        simp [hExpr]
    calc
      (∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν) ≤
          ∫⁻ z in Iio (0 : ℝ),
            ENNReal.ofReal K *
              ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν := by
              apply setLIntegral_mono (by fun_prop)
              intro z hz
              exact hbound z hz
      _ ≤ ∫⁻ z : ℝ,
          ENNReal.ofReal K *
            ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν :=
        setLIntegral_le_lintegral _ _
      _ = ENNReal.ofReal K *
          (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) :=
        lintegral_const_mul _ hνmeas
  have houter :
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) ≤
        μ Set.univ *
          (ENNReal.ofReal K *
            (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν)) := by
    calc
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((H (p, z)) ^ 2) ∂X.ν ∂μ) ≤
          ∫⁻ _ : ℝ≥0 × Ω,
            ENNReal.ofReal K *
              (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν) ∂μ :=
            lintegral_mono hinner
      _ = μ Set.univ *
            (ENNReal.ofReal K *
              (∫⁻ z : ℝ, ENNReal.ofReal (min 1 (z ^ 2)) ∂X.ν)) := by
              simp [mul_comm]
  exact lt_of_le_of_lt houter (ENNReal.mul_lt_top hμ hM)
