-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_thinned_C2_generator_kernel_L1_identification
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T17:46:35.6082+00:00
-- url     : https://prove2.me/submissions/ad6b68dc-5fa2-4d7b-a897-ab3c08c6242a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_07_original_C2_joint_predictable_thinned_drift_integrable
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_source_taylor_generator_kernel_eq

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Any jointly predictable thinning identifies the stopped nonlinear Taylor
compensator with the original negative Lévy generator drift, in Bochner L1. -/
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
    (S : Set ((ℝ≥0 × Ω) × ℝ))
    (hS : MeasurableSet[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] S) :
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
    let G : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Integrable (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν) μ ∧
    (∀ p : ℝ≥0 × Ω,
      (∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) =
      (∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν)) := by
  classical
  intro Y H HS G
  have hBase :=
    avram_wave7_07_original_C2_joint_predictable_thinned_drift_integrable
      X x D hD w C u v δ hw hw_cont hw_neg hu hδ hδone huv hv μ hμ S hS
  have hPoint (p : ℝ≥0 × Ω) (z : ℝ) (hz : z < 0) :
      HS (p,z) = G (p,z) := by
    have hKernel :=
      avram_wave5_03b_actual_source_taylor_generator_kernel_eq
        X x D hD w u v δ p z hz
    dsimp [HS, G, H]
    exact congrArg (fun t : ℝ =>
      (if (p.1 : ℝ≥0∞) ≤ ruinTime X x D p.2 then (1 : ℝ) else 0) * t)
      hKernel
  have hIntegral (p : ℝ≥0 × Ω) :
      (∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) =
      (∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν) := by
    apply setIntegral_congr_fun measurableSet_Iio
    intro z hz
    by_cases hp : (p,z) ∈ S
    · simpa only [Set.indicator_of_mem hp] using hPoint p z hz
    · simp only [Set.indicator_of_notMem hp]
  constructor
  · have hFunEq :
        (fun p : ℝ≥0 × Ω =>
          ∫ z in Iio (0 : ℝ), (S.indicator G) (p,z) ∂X.ν) =
        (fun p : ℝ≥0 × Ω =>
          ∫ z in Iio (0 : ℝ), (S.indicator HS) (p,z) ∂X.ν) := by
      funext p
      exact (hIntegral p).symm
    rw [hFunEq]
    exact hBase.2
  · exact hIntegral
