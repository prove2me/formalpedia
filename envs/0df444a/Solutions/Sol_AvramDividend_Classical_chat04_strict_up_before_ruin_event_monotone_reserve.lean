-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_up_before_ruin_event_monotone_reserve
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T15:08:37.785836+00:00
-- url     : https://prove2.me/submissions/5026541c-46c5-4a75-816a-d294e4359ce7

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_monotone_initial_reserve
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A successful strict upper exit remains successful with greater initial capital. -/
theorem solution {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (a x y : ℝ) (hxy : x ≤ y) :
    {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ⊆
    {ω : Ω | twoSidedExitUpTime X (a - y) ω <
      twoSidedExitDownTime X (-y) ω} := by
  intro ω hsuccess
  obtain ⟨hup, hdown⟩ :=
    chat04_strict_exit_clocks_monotone_initial_reserve X a x y hxy ω
  exact lt_of_le_of_lt hup (lt_of_lt_of_le hsuccess hdown)
