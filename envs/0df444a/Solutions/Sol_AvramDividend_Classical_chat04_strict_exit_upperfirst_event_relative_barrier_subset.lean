-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_exit_upperfirst_event_relative_barrier_subset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:22:40.429182+00:00
-- url     : https://prove2.me/submissions/f2a6e325-0109-4f50-80e1-e4a9f47ce9c2

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- If the initial reserve rises and the upper boundary is no farther in relative terms, every trajectory exiting above before ruin in the original system also exits above before ruin in the shifted system. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ⊆
    {ω : Ω | twoSidedExitUpTime X (b - y) ω <
      twoSidedExitDownTime X (-y) ω} := by
  intro ω h
  obtain ⟨hu, hd⟩ :=
    chat04_strict_exit_clocks_relative_barrier_comparison
      X a b x y hxy hrel ω
  exact lt_of_lt_of_le (lt_of_le_of_lt hu h) hd
