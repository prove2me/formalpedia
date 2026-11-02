-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_03b_actual_ruin_stopped_full_negative_C2_generator_signed_drift_predictable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T11:14:12.956324+00:00
-- url     : https://prove2.me/submissions/97e304f4-76d0-419e-81b9-56c5b52bc05f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The signed original-source jump generator drift of the actual stopped
controlled reserve is measurable for the right-continuous predictable sigma
algebra, with genuine X.nu and no independent Poisson replacement. -/
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
    (huv : u + δ < v) (hv : v < C) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1
    let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
      (if Y p.1 ∈ Icc (u + δ) v then
        SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) := by
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
  let JG : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
    (if (p.1.1 : ℝ≥0∞) ≤ ruinTime X x D p.1.2 then (1 : ℝ) else 0) *
    (if Y p.1 ∈ Icc (u + δ) v then
      SpectrallyNegativeLevy.generatorIntegrand w (Y p.1) p.2 else 0)
  change Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
    ∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν)
  let μ0 : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable) := 0
  have hμ0 : μ0 Set.univ < ⊤ := by simp [μ0]
  have hpred : Measurable[(𝓕.rightCont.predictable).prod
      (inferInstance : MeasurableSpace ℝ)] HS :=
    (avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
      X x D hD w C u v δ hw hw_cont hw_neg
      hu hδ hδone huv hv μ0 hμ0).1
  letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
  letI : MeasurableSpace ((ℝ≥0 × Ω) × ℝ) :=
    (𝓕.rightCont.predictable).prod (inferInstance : MeasurableSpace ℝ)
  letI : SFinite (X.ν.restrict (Iio (0 : ℝ))) :=
    levy_negative_jump_measure_sFinite X
  have hstrong : StronglyMeasurable HS := hpred.stronglyMeasurable
  have hsection : StronglyMeasurable (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ), HS (p,z) ∂X.ν) :=
    StronglyMeasurable.integral_prod_right
      (ν := X.ν.restrict (Iio (0 : ℝ))) hstrong
  have heq (p : ℝ≥0 × Ω) :
      (∫ z in Iio (0 : ℝ), HS (p,z) ∂X.ν) =
      (∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) := by
    simpa [HS, H, JG, Y] using
      (avram_wave5_03b_actual_ruin_stopped_source_generator_jump_drift_integral_eq
        X x D hD w u v δ p (Iio (0 : ℝ))
        measurableSet_Iio (Subset.rfl))
  have heqfun :
      (fun p : ℝ≥0 × Ω => ∫ z in Iio (0 : ℝ), JG (p,z) ∂X.ν) =
      (fun p : ℝ≥0 × Ω => ∫ z in Iio (0 : ℝ), HS (p,z) ∂X.ν) := by
    funext p
    exact (heq p).symm
  rw [heqfun]
  exact hsection.measurable
