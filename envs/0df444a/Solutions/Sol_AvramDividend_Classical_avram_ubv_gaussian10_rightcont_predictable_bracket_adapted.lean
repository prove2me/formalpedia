-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_rightcont_predictable_bracket_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:22:41.821358+00:00
-- url     : https://prove2.me/submissions/9e6a0305-69a0-4947-b6bc-e0e17a31dce1

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_rightcont_predictable_band_trace

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The true right-continuous stopping filtration carries the squared bracket
of a predictable Gaussian coefficient without filtration augmentation. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : Measurable[𝓕.rightCont.predictable] H)
    (μtime : Measure ℝ≥0) [SFinite μtime] :
    Adapted 𝓕.rightCont (fun b ω =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime) := by
  intro b
  let mBand : MeasurableSpace (ℝ≥0 × Ω) :=
    @Prod.instMeasurableSpace ℝ≥0 Ω inferInstance (𝓕.rightCont b)
  let band : Set (ℝ≥0 × Ω) := Ioc (0 : ℝ≥0) b ×ˢ (univ : Set Ω)
  have hBandSet : MeasurableSet[mBand] band :=
    measurableSet_Ioc.prod (@MeasurableSet.univ Ω (𝓕.rightCont b))
  have hsq : Measurable[𝓕.rightCont.predictable] (fun z => (H z) ^ 2) :=
    hH.pow_const 2
  have hc : Measurable[mBand] (band.indicator (fun z => (H z) ^ 2)) := by
    intro A hA
    rw [Set.indicator_preimage]
    refine MeasurableSet.union ?_ ?_
    · exact avram_ubv_gaussian10_original_rightcont_predictable_band_trace
        X 0 b ((fun z => (H z) ^ 2) ⁻¹' A) (hsq hA)
    · by_cases h0 : (0 : ℝ) ∈ A
      · rw [show (0 : ℝ≥0 × Ω → ℝ) ⁻¹' A = Set.univ
          from Set.eq_univ_of_forall fun _ => h0,
          ← Set.compl_eq_univ_sdiff]
        exact hBandSet.compl
      · rw [show (0 : ℝ≥0 × Ω → ℝ) ⁻¹' A = ∅
          from Set.eq_empty_iff_forall_notMem.mpr fun _ hx => h0 hx,
          Set.empty_sdiff]
        exact @MeasurableSet.empty _ mBand
  have hm : Measurable[𝓕.rightCont b]
      (fun ω => ∫ t,
        (band.indicator (fun z => (H z) ^ 2)) (t, ω) ∂μtime) := by
    letI : MeasurableSpace Ω := 𝓕.rightCont b
    exact ((hc.comp measurable_swap).stronglyMeasurable.integral_prod_right').measurable
  convert hm using 1
  funext ω
  change (∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime) =
    ∫ t, (band.indicator (fun z => (H z) ^ 2)) (t, ω) ∂μtime
  rw [← integral_indicator measurableSet_Ioc]
  apply integral_congr_ae
  filter_upwards [] with t
  by_cases ht : t ∈ Ioc (0 : ℝ≥0) b
  · simp [band, Set.indicator_of_mem, ht]
  · simp [band, Set.indicator_of_notMem, ht]