-- Prove2me | solution 1 for AvramDividend.Classical.avram_pj_original_stopped_clipped_predictable_coefficient_later_rightCont_stronglyMeasurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-20T12:26:21.52304+00:00
-- url     : https://prove2.me/submissions/a6fbfb47-74e2-4347-b845-13aa597f0afe

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_clipped_stronglyPredictable_bounded
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual predictable stopped and clipped physical-grid
coefficient is strongly measurable in every subsequent original
right-continuous filtration. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (Z : ℝ≥0 → Ω → ℝ)
    (hZ : IsStronglyPredictable 𝓕.rightCont Z)
    (K : ℝ) (hK : 0 ≤ K)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (ρ ω : WithTop ℝ≥0)))
    (s t : ℝ≥0) (hst : s ≤ t) :
    StronglyMeasurable[𝓕.rightCont t] (fun ω =>
      if (ρ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)
      then (0 : ℝ) else max (-K) (min K (Z s ω))) := by
  obtain ⟨hPredictable, hBound⟩ :=
    avram_wave3_04_clipped_stronglyPredictable_bounded Z hZ K hK
  have hClip : Measurable[𝓕.rightCont s] (fun ω =>
      max (-K) (min K (Z s ω))) :=
    (hPredictable.stronglyAdapted s).measurable
  have hSet : MeasurableSet[𝓕.rightCont s]
      {ω : Ω | (ρ ω : WithTop ℝ≥0) ≤
        (s : WithTop ℝ≥0)} :=
    hρstop.measurableSet_le s
  have hMask : Measurable[𝓕.rightCont s] (fun ω =>
      if (ρ ω : WithTop ℝ≥0) ≤ (s : WithTop ℝ≥0)
      then (0 : ℝ) else max (-K) (min K (Z s ω))) :=
    measurable_const.ite hSet hClip
  exact (hMask.mono (𝓕.rightCont.mono hst) le_rfl).stronglyMeasurable
