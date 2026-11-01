-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave4_01_original_first_record_height_clock_measurable
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-31T16:19:41.118665+00:00
-- url     : https://prove2.me/submissions/2bc8702d-55cf-437a-bb5c-b2407b8c352b

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_twoSidedExitUpTime_mono_threshold
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Topology

/-- The genuine strict first-record clock is measurable in its height, pathwise. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    Measurable (fun h : ℝ => twoSidedExitUpTime X h ω) := by
  apply Monotone.measurable
  intro a b hab
  exact twoSidedExitUpTime_mono_threshold X a b hab ω
