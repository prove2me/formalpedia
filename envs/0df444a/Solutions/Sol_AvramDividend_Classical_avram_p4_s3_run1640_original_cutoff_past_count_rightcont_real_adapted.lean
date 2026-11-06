-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_s3_run1640_original_cutoff_past_count_rightcont_real_adapted
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-05T16:56:14.503866+00:00
-- url     : https://prove2.me/submissions/403398c5-943f-4041-affc-2d25997914af

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_f_assembly_original_past_count_raw_measurable_auto
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual real-valued past negative-cutoff count is adapted at its original right-continuous horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    StronglyMeasurable[𝓕.rightCont T]
      (fun ω : Ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal) := by
  have hRaw := avram_p4_f_assembly_original_past_count_raw_measurable_auto X T n
  have hReal : Measurable[𝓕 T]
      (fun ω : Ω =>
      (((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-(1 / ((n : ℝ) + 1))))).toReal) :=
    ENNReal.measurable_toReal.comp hRaw
  have hLE : 𝓕 T ≤ 𝓕.rightCont T :=
    (Filtration.le_rightCont 𝓕) T
  exact (hReal.mono hLE le_rfl).stronglyMeasurable
