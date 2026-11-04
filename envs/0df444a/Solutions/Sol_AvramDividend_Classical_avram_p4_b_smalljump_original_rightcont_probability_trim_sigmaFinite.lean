-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_rightcont_probability_trim_sigmaFinite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:34:26.195327+00:00
-- url     : https://prove2.me/submissions/043492ee-c49a-401e-aa06-8beb69ecb52f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The actual right-continuous source filtration has sigma-finite trimmed
probability measures, discharging the condition on L2 martingale closure. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    (𝓕 : Filtration ℝ≥0 mΩ) :
    ∀ s : ℝ≥0,
      @SigmaFinite Ω (𝓕.rightCont s) (P.trim (𝓕.rightCont.le s)) := by
  intro s
  letI : MeasurableSpace Ω := 𝓕.rightCont s
  letI : IsFiniteMeasure (P.trim (𝓕.rightCont.le s)) :=
    isFiniteMeasure_trim (𝓕.rightCont.le s)
  infer_instance
