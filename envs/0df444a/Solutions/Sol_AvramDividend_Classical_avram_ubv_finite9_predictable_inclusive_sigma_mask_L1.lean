-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_finite9_predictable_inclusive_sigma_mask_L1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T17:37:44.941112+00:00
-- url     : https://prove2.me/submissions/3bc428ff-7672-4101-af35-b30610535c1e

import Mathlib.Probability.Process.Stopping
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p3_b_bvjump_original_predictable_le_product_space
import Theorems.Thm_AvramDividend_Classical_avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal

noncomputable section

/-- An original right-continuous stopping mask preserves physical time-integrated L1. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (T : ℝ≥0)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμclock : ∀ A : Set (ℝ≥0 × Ω),
      MeasurableSet[𝓕.rightCont.predictable] A →
      μ A = ((((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal).prod P) A)
    (G : ℝ≥0 × Ω → ℝ)
    (hGI : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable; Integrable G μ))
    (σ : Ω → ℝ≥0)
    (hσstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (σ ω : WithTop ℝ≥0))) :
    Integrable (fun ω =>
      ∫ t : ℝ≥0,
        if t ≤ σ ω then G (t, ω) else 0
      ∂(((volume : Measure ℝ).restrict
        (Icc 0 (T : ℝ))).map Real.toNNReal)) P := by
  classical
  let θ : Measure ℝ≥0 :=
    ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))).map Real.toNNReal
  haveI hFiniteTime : IsFiniteMeasure
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) := by
    infer_instance
  haveI hFiniteθ : IsFiniteMeasure θ :=
    Measure.isFiniteMeasure_map
      ((volume : Measure ℝ).restrict (Icc 0 (T : ℝ))) Real.toNNReal
  let ν : Measure (ℝ≥0 × Ω) := θ.prod P
  let S : Set (ℝ≥0 × Ω) := {p | p.1 ≤ σ p.2}
  have hPred : 𝓕.rightCont.predictable ≤
      (inferInstance : MeasurableSpace (ℝ≥0 × Ω)) :=
    avram_p3_b_bvjump_original_predictable_le_product_space 𝓕
  have hSm : MeasurableSet[𝓕.rightCont.predictable] S := by
    exact avram_wave4_p1_nnreal_stopping_inclusive_predictable_mask
      𝓕.rightCont σ hσstop
  have hμtrim : μ = ν.trim hPred := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    ext A hA
    rw [trim_measurableSet_eq hPred hA]
    exact hμclock A hA
  have hMaskI : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable; Integrable (S.indicator G) μ) := by
    letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable
    exact hGI.indicator hSm
  have hTrimI : (letI : MeasurableSpace (ℝ≥0 × Ω) :=
      𝓕.rightCont.predictable; Integrable (S.indicator G) (ν.trim hPred)) := by
    simpa only [← hμtrim] using hMaskI
  have hProdI : Integrable (S.indicator G) ν :=
    integrable_of_integrable_trim hPred hTrimI
  have hRight : Integrable (fun ω =>
      ∫ t : ℝ≥0, (S.indicator G) (t, ω) ∂θ) P :=
    hProdI.integral_prod_right
  have hTarget : Integrable (fun ω =>
      ∫ t : ℝ≥0, if t ≤ σ ω then G (t, ω) else 0 ∂θ) P := by
    convert hRight using 1
    ext ω
    apply integral_congr_ae
    filter_upwards [] with t
    by_cases ht : t ≤ σ ω
    · simp [S, Set.indicator, ht]
    · simp [S, Set.indicator, ht]
  simpa only [θ] using hTarget
