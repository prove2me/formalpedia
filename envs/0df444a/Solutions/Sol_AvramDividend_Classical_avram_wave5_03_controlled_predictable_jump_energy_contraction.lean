-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03_controlled_predictable_jump_energy_contraction
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:59:47.312366+00:00
-- url     : https://prove2.me/submissions/e1a13e54-0c85-43f8-9e4f-e6e7c4b4f90f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Bounded predictable-mark multipliers preserve the actual controlled source Lévy jump energy. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v δ : ℝ)
    (hw : ContDiffOn ℝ 1 w (Ioo a b))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (hu0 : 0 ≤ u)
    (hδ : 0 < δ) (hδone : δ ≤ 1) (hband : u + δ ≤ v)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (K : ((ℝ≥0 × Ω) × ℝ) → ℝ)
    (hK : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] K)
    (hKbound : ∀ p, |K p| ≤ 1) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] (fun p => K p * J p) ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((K (p, z) * J (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ := by
  dsimp only
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0
  change Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] (fun p => K p * J p) ∧
    (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((K (p, z) * J (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤
  have hJ :=
    avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
      X x D hD w a b u v δ hw hw_cont hw_neg
      hau huv hvb hu0 hδ hδone hband μ hμ
  refine ⟨hK.mul hJ.1, ?_⟩
  have hpoint (p : (ℝ≥0 × Ω) × ℝ) :
      (K p * J p) ^ 2 ≤ (J p) ^ 2 := by
    have hlo : -1 ≤ K p := (abs_le.mp (hKbound p)).1
    have hhi : K p ≤ 1 := (abs_le.mp (hKbound p)).2
    have hprod : 0 ≤ (1 - K p) * (1 + K p) :=
      mul_nonneg (sub_nonneg.mpr hhi) (by linarith)
    have hsq : (K p) ^ 2 ≤ 1 := by nlinarith [hprod]
    calc
      (K p * J p) ^ 2 = (K p) ^ 2 * (J p) ^ 2 := by ring
      _ ≤ 1 * (J p) ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (sq_nonneg _)
      _ = (J p) ^ 2 := by ring
  calc
    (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((K (p, z) * J (p, z)) ^ 2) ∂X.ν ∂μ) ≤
      (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((J (p, z)) ^ 2) ∂X.ν ∂μ) := by
        apply lintegral_mono
        intro p
        apply lintegral_mono
        intro z
        exact ENNReal.ofReal_le_ofReal (hpoint (p, z))
    _ < ⊤ := hJ.2
