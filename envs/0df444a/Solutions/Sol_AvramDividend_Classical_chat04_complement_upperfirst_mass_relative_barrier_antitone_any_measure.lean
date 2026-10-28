-- Prove2me | solution 1 for AvramDividend.Classical.chat04_complement_upperfirst_mass_relative_barrier_antitone_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:56:49.514864+00:00
-- url     : https://prove2.me/submissions/ba22a601-d086-4a5c-baa7-28282a9b6b39

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_upperfirst_event_relative_barrier_subset

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Under a relative reserve increase the mass failing strict upper-first exit cannot increase. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    μ {ω : Ω | ¬ (twoSidedExitUpTime X (b - y) ω <
      twoSidedExitDownTime X (-y) ω)} ≤
    μ {ω : Ω | ¬ (twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω)} := by
  apply measure_mono
  intro ω hn hE
  exact hn
    ((chat04_strict_exit_upperfirst_event_relative_barrier_subset
      X a b x y hxy hrel) hE)
