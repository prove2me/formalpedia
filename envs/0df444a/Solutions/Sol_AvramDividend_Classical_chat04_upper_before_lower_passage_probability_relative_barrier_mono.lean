-- Prove2me | solution 1 for AvramDividend.Classical.chat04_upper_before_lower_passage_probability_relative_barrier_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T10:48:40.850991+00:00
-- url     : https://prove2.me/submissions/3705f7bd-a834-4062-819d-0211c174311b

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

/-- Upper exit before strict ruin is monotone under reserve-compensated barrier shifts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    P {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ≤
      P {ω : Ω | twoSidedExitUpTime X (b - y) ω <
        twoSidedExitDownTime X (-y) ω} := by
  apply measure_mono
  intro ω hω
  obtain ⟨hup, hdown⟩ :=
    chat04_strict_exit_clocks_relative_barrier_comparison
      X a b x y hxy hrel ω
  exact lt_of_le_of_lt hup (lt_of_lt_of_le hω hdown)
