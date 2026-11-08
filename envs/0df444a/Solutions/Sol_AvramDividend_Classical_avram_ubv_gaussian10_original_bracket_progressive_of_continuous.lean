-- Prove2me | solution 1 for AvramDividend.Classical.avram_ubv_gaussian10_original_bracket_progressive_of_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-07T11:35:27.951871+00:00
-- url     : https://prove2.me/submissions/d84033a7-a543-460b-a707-d00a972aa372

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_rightcont_predictable_bracket_adapted

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The adapted bracket from the same original right-continuous filtration
is progressively measurable when its individual time paths are continuous. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0 × Ω → ℝ)
    (hH : Measurable[𝓕.rightCont.predictable] H)
    (μtime : Measure ℝ≥0) [SFinite μtime]
    (hContinuous : ∀ ω, Continuous (fun b : ℝ≥0 =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime)) :
    IsStronglyProgressive 𝓕.rightCont (fun b ω =>
      ∫ t in Ioc (0 : ℝ≥0) b, (H (t, ω)) ^ 2 ∂μtime) := by
  exact (avram_ubv_gaussian10_rightcont_predictable_bracket_adapted
    X H hH μtime).stronglyAdapted.isStronglyProgressive_of_continuous
      hContinuous
