-- Prove2me | solution 1 for AvramDividend.Classical.unbounded_positive_level_upcrossing_strictly_before_horizon
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T20:32:19.05557+00:00
-- url     : https://prove2.me/submissions/fa127ea4-bf1b-4872-8c3a-334222c98ad9

import Theorems.Thm_AvramDividend_Classical_unbounded_positive_level_upcrossing_before_horizon
import Mathlib.Tactic.NormNum
import Mathlib.MeasureTheory.OuterMeasure.Basic
import Mathlib.MeasureTheory.MeasurableSpace.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

/-- A positive threshold is crossed with positive probability at some
strictly earlier observation time than any given positive horizon. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q) (hnbv : ¬ X.BoundedVariation)
    (t : ℝ≥0) (ht : 0 < t) :
    ∃ a : ℝ, 0 < a ∧
      0 < P {ω : Ω | ∃ s : ℝ≥0, s < t ∧ a < X.X s ω} := by
  have ht2 : (0 : ℝ≥0) < t / 2 := div_pos ht (by norm_num)
  have ht2lt : t / 2 < t := div_lt_self ht (by norm_num)
  obtain ⟨a, ha, hprob⟩ :=
    unbounded_positive_level_upcrossing_before_horizon
      X q hq hnbv (t / 2) ht2
  refine ⟨a, ha, ?_⟩
  have hsub :
      {ω : Ω | ∃ s : ℝ≥0, s ≤ t / 2 ∧ a < X.X s ω} ⊆
        {ω : Ω | ∃ s : ℝ≥0, s < t ∧ a < X.X s ω} := by
    rintro ω ⟨s, hs, haω⟩
    exact ⟨s, lt_of_le_of_lt hs ht2lt, haω⟩
  exact lt_of_lt_of_le hprob (measure_mono hsub)
