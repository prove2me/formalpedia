-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_lowerfirst_event_relative_barrier_subset
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:59:01.030912+00:00
-- url     : https://prove2.me/submissions/3fa60396-1333-4e95-b887-075e1acc2aba

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Ruin strictly before upper exit in the higher-reserve system implies the same in the lower-reserve system. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    {ω : Ω | twoSidedExitDownTime X (-y) ω <
      twoSidedExitUpTime X (b - y) ω} ⊆
    {ω : Ω | twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a - x) ω} := by
  intro ω h
  obtain ⟨hu, hd⟩ :=
    chat04_strict_exit_clocks_relative_barrier_comparison
      X a b x y hxy hrel ω
  exact lt_of_le_of_lt hd (lt_of_lt_of_le h hu)
