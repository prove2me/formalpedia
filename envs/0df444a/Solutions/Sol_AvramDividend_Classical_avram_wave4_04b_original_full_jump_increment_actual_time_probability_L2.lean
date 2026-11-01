-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_04b_original_full_jump_increment_actual_time_probability_L2
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T00:44:38.730706+00:00
-- url     : https://prove2.me/submissions/407102f1-cbdc-4abd-94e6-8ee3d367c3f7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_negative_levy_measure_sigmaFinite
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite

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
    (T : ℝ≥0) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
      fun p => if Y p.1 ∈ Icc (u + δ) v then
        w (Y p.1 + p.2) - w (Y p.1) else 0
    Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] J ∧
      (∫⁻ p : ℝ≥0 × Ω,
        ∫⁻ z in Iio (0 : ℝ),
          ENNReal.ofReal ((J (p, z)) ^ 2) ∂X.ν
          ∂((((volume : Measure ℝ).restrict
            (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) < ⊤ := by
  dsimp only
  classical
  let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
    (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
  let J : ((ℝ≥0 × Ω) × ℝ) → ℝ :=
    fun p => if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0
  change Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] J ∧
    (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((J (p, z)) ^ 2) ∂X.ν
      ∂((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) < ⊤
  obtain ⟨μ, hμ, _hμeq, hlintegral⟩ :=
    avram_wave4_04b_source_finite_horizon_predictable_lintegral_eq_time_probability X T
  have hw1 : ContDiffOn ℝ 1 w (Ioo a b) := hw.of_le (by norm_num)
  have hJ :=
    avram_wave4_04_controlled_predictable_full_negative_mark_energy_finite
      X x D hD w a b u v δ hw1 hw_cont hw_neg
      hau huv hvb hu0 hδ hδone hband μ hμ
  have hJmeas : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] J := hJ.1
  have henergy :
      (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((J (p, z)) ^ 2) ∂X.ν ∂μ) < ⊤ :=
    hJ.2
  refine ⟨hJmeas, ?_⟩
  have hlevy : (∫⁻ y in Iio (0 : ℝ),
      ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) < ⊤ := by
    calc
      (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) ≤
          (∫⁻ y : ℝ, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) := by
        simpa using (lintegral_mono_set
          (Set.subset_univ (Iio (0 : ℝ))) :
          (∫⁻ y in Iio (0 : ℝ), ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν) ≤
            ∫⁻ y in Set.univ, ENNReal.ofReal (min 1 (y ^ 2)) ∂X.ν)
      _ < ⊤ := X.ν_integrable
  letI : SigmaFinite X.ν :=
    avram_wave4_04b_negative_levy_measure_sigmaFinite X.ν X.ν_Ici hlevy
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)
  have hφ : Measurable (fun p : ((ℝ≥0 × Ω) × ℝ) =>
      ENNReal.ofReal ((J p) ^ 2)) :=
    (hJmeas.pow_const 2).ennreal_ofReal
  have hFmeas : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω => ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((J (p, z)) ^ 2) ∂X.ν) := by
    exact Measurable.lintegral_prod_right' hφ
  calc
    (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
      ENNReal.ofReal ((J (p, z)) ^ 2) ∂X.ν
      ∂((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P)) =
      (∫⁻ p : ℝ≥0 × Ω, ∫⁻ z in Iio (0 : ℝ),
        ENNReal.ofReal ((J (p, z)) ^ 2) ∂X.ν ∂μ) := by
        exact (hlintegral _ hFmeas).symm
    _ < ⊤ := henergy
