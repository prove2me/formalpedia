-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_predictable_borel_negative_generator_mark_integral_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T21:38:28.583703+00:00
-- url     : https://prove2.me/submissions/9a98a026-b26d-4c0a-a6f9-9050cd562888

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C u v δ : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo 0 C))
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y : ℝ, y < 0 → w y = 0)
    (hu : 0 < u) (hδ : 0 < δ) (hδone : δ ≤ 1)
    (huv : u + δ < v) (hv : v < C)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (B : Set ℝ) (hBm : MeasurableSet B)
    (hBneg : B ⊆ Iio (0 : ℝ)) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      ∫ z in B, G (p,z) ∂X.ν) := by
  classical
  intro Y G
  let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if Y p.1 ∈ Icc (u + δ) v then
      w (Y p.1 + p.2) - w (Y p.1) else 0) -
    (if -1 < p.2 then
      p.2 * (if Y p.1 ∈ Icc (u + δ) v then deriv w (Y p.1) else 0)
      else 0)
  let HS : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) * H p
  let S : Set ((ℝ≥0 × Ω) × ℝ) := {r | r.2 ∈ B}
  have hS :
      MeasurableSet[(𝓕.rightCont.predictable).prod
        (inferInstance : MeasurableSpace ℝ)] S := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    exact hBm.preimage measurable_snd
  have hRestrict :
      (X.ν.restrict (Iio (0 : ℝ))).restrict B = X.ν.restrict B := by
    rw [Measure.restrict_restrict hBm]
    congr 1
    exact Set.inter_eq_left.mpr hBneg
  have hInner (p : ℝ≥0 × Ω) :
      (∫ z in B, G (p,z) ∂X.ν) =
      (∫ z in Iio (0 : ℝ), S.indicator G (p,z) ∂X.ν) := by
    symm
    calc
      (∫ z in Iio (0 : ℝ), S.indicator G (p,z) ∂X.ν) =
          ∫ z : ℝ, B.indicator (fun z => G (p,z)) z
            ∂(X.ν.restrict (Iio (0 : ℝ))) := rfl
      _ = ∫ z : ℝ, G (p,z)
            ∂((X.ν.restrict (Iio (0 : ℝ))).restrict B) :=
              integral_indicator hBm
      _ = ∫ z in B, G (p,z) ∂X.ν := by rw [hRestrict]
  have hThin :=
    avram_wave7_07_original_stopped_C2_joint_predictable_thinning_finite_energy
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv μ hμ S hS
  have hKernel :=
    avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv μ hμ S hS
  have hFnEq :
      (fun p : ℝ≥0 × Ω =>
        ∫ z in Iio (0 : ℝ), S.indicator HS (p,z) ∂X.ν) =
      (fun p : ℝ≥0 × Ω =>
        ∫ z in Iio (0 : ℝ), S.indicator G (p,z) ∂X.ν) :=
    funext hKernel.2
  have hMeasG : Measurable[𝓕.rightCont.predictable]
      (fun p : ℝ≥0 × Ω =>
        ∫ z in Iio (0 : ℝ), S.indicator G (p,z) ∂X.ν) :=
    hFnEq ▸ hThin.1
  exact (funext hInner).symm ▸ hMeasG
