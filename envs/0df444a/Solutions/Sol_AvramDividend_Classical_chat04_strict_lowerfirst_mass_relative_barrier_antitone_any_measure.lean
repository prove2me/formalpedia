-- Prove2me | solution 1 for AvramDividend.Classical.chat04_strict_lowerfirst_mass_relative_barrier_antitone_any_measure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T11:59:22.365995+00:00
-- url     : https://prove2.me/submissions/e1851d68-4ce3-4720-b9f9-93c18a5d3eea

import Mathlib.MeasureTheory.Measure.MeasureSpace
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_clocks_relative_barrier_comparison

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- Under an improving relative reserve, the strict ruin-before-upper-exit mass cannot increase. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (μ : Measure Ω)
    (a b x y : ℝ) (hxy : x ≤ y) (hrel : b - y ≤ a - x) :
    μ {ω : Ω | twoSidedExitDownTime X (-y) ω <
      twoSidedExitUpTime X (b - y) ω} ≤
    μ {ω : Ω | twoSidedExitDownTime X (-x) ω <
      twoSidedExitUpTime X (a - x) ω} := by
  apply measure_mono
  intro ω h
  obtain ⟨hu, hd⟩ :=
    chat04_strict_exit_clocks_relative_barrier_comparison
      X a b x y hxy hrel ω
  exact lt_of_le_of_lt hd (lt_of_lt_of_le h hu)
