-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_variation_standing_iff_integrable_one
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-22T05:16:08.435987+00:00
-- url     : https://prove2.me/submissions/09b43354-646e-4806-a4e0-dc879af25ed3

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
    X.Standing ↔ Integrable (X.X 1) P := by
  constructor
  · intro hstanding
    exact hstanding.2.1
  · intro hInt
    have hnotmono : ¬ X.HasMonotonePaths := by
      intro hmono
      exact hnbv hmono.1
    have hcondition : X.Condition33 := by
      rcases unbounded_variation_gaussian_or_infinite_small_jump_moment X hnbv with hσ | hsmall
      · exact Or.inl hσ
      · exact Or.inr (Or.inl hsmall)
    exact ⟨hnotmono, hInt, hcondition⟩
