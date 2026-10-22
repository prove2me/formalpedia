-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_variation_condition33_no_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T05:13:01.222857+00:00
-- url     : https://prove2.me/submissions/df19a3c6-a862-4754-bd3b-8edf804c61ba

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_unbounded_variation_gaussian_or_infinite_small_jump_moment
import Mathlib.MeasureTheory.MeasurableSpace.Defs
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ¬ X.HasMonotonePaths ∧ X.Condition33 := by
  constructor
  · intro hmono
    exact hnbv hmono.1
  · rcases unbounded_variation_gaussian_or_infinite_small_jump_moment X hnbv with hσ | hsmall
    · exact Or.inl hσ
    · exact Or.inr (Or.inl hsmall)
