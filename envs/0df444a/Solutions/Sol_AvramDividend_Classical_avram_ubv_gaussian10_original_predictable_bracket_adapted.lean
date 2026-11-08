-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_predictable_bracket_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:14:12.768448+00:00
-- url     : https://prove2.me/submissions/dcd1177b-9639-4acc-80a4-ea6115025b28

import Mathlib.Probability.Process.Adapted
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_predictable_band_trace
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_filtration_bracket_adapted_sfinite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- A predictable Gaussian coefficient has an adapted pathwise squared bracket
on Avram's original filtration, for every sigma-finite time measure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : Measurable[𝓕.predictable] H)
    (μtime : Measure ℝ≥0) [SFinite μtime] :
    Adapted 𝓕 (fun b ω =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime) := by
  apply avram_ubv_gaussian10_original_filtration_bracket_adapted_sfinite
    X (fun z : Ω × ℝ≥0 => H (z.2, z.1)) μtime
  intro b
  let mBand : MeasurableSpace (ℝ≥0 × Ω) :=
    @Prod.instMeasurableSpace ℝ≥0 Ω inferInstance (𝓕 b)
  let band : Set (ℝ≥0 × Ω) := Ioc (0 : ℝ≥0) b ×ˢ (univ : Set Ω)
  have hBandSet : MeasurableSet[mBand] band :=
    measurableSet_Ioc.prod (@MeasurableSet.univ Ω (𝓕 b))
  have hsq : Measurable[𝓕.predictable] (fun z => (H z) ^ 2) :=
    hH.pow_const 2
  have hc : Measurable[mBand] (band.indicator (fun z => (H z) ^ 2)) := by
    intro A hA
    rw [Set.indicator_preimage]
    refine MeasurableSet.union ?_ ?_
    · exact avram_ubv_gaussian10_original_predictable_band_trace
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
  have hs : Measurable[
      @Prod.instMeasurableSpace Ω ℝ≥0 (𝓕 b) inferInstance]
      (fun z : Ω × ℝ≥0 =>
        (band.indicator (fun p => (H p) ^ 2)) (z.2, z.1)) := by
    exact hc.comp measurable_swap
  convert hs using 1
  funext z
  rcases z with ⟨ω, t⟩
  by_cases ht : t ∈ Ioc (0 : ℝ≥0) b
  · simp [band, Set.indicator_of_mem, ht]
  · simp [band, Set.indicator_of_notMem, ht]