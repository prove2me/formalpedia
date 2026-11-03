-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_07_original_stopped_C2_joint_predictable_mark_thinning_drift
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:11:50.673203+00:00
-- url     : https://prove2.me/submissions/1cc7ae4c-b81e-4180-a71d-f69a112900f0

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03b_actual_ruin_stopped_full_negative_C2_taylor_predictable_L1_L2
import Theorems.Thm_AvramDividend_Classical_levy_negative_jump_measure_sFinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Predictable thinning of the actual stopped C² Taylor generator correction
by an arbitrary jointly predictable mark set, on the genuine source ν. -/
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
    Measurable[𝓕.rightCont.predictable] (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ),
        (S.indicator HS) (p,z) ∂X.ν) := by
  classical
  intro Y H HS
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
  have hthin : Measurable (S.indicator HS) :=
    hpred.indicator hS
  have hsection : StronglyMeasurable (fun p : ℝ≥0 × Ω =>
      ∫ z in Iio (0 : ℝ),
        (S.indicator HS) (p,z) ∂X.ν) :=
    StronglyMeasurable.integral_prod_right
      (ν := X.ν.restrict (Iio (0 : ℝ))) hthin.stronglyMeasurable
  exact hsection.measurable
