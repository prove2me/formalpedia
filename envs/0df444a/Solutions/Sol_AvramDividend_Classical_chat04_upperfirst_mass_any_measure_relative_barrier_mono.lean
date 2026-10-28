-- Prove2me | solution 1 for AvramDividend.Classical.chat04_upperfirst_mass_any_measure_relative_barrier_mono
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:22:43.163778+00:00
-- url     : https://prove2.me/submissions/31c466c0-65e3-4e23-9c26-eb38b95c61a3

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Under any measure on the path space, a reserve increase compensating the change in upper barrier can only increase the mass of paths that cross the upper barrier before ruin. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    μ {ω : Ω | twoSidedExitUpTime X (a - x) ω <
      twoSidedExitDownTime X (-x) ω} ≤
    μ {ω : Ω | twoSidedExitUpTime X (b - y) ω <
      twoSidedExitDownTime X (-y) ω} := by
  apply measure_mono
  intro ω h
  obtain ⟨hu, hd⟩ :=
    chat04_strict_exit_clocks_relative_barrier_comparison
      X a b x y hxy hrel ω
  exact lt_of_lt_of_le (lt_of_le_of_lt hu h) hd
