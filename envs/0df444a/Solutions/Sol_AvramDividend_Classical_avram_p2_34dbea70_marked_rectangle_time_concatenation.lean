-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_marked_rectangle_time_concatenation
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T13:22:11.750383+00:00
-- url     : https://prove2.me/submissions/76ad15e2-99eb-4438-8ad4-4c267238b2fb

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- A marked counting measure splits over consecutive right-closed time windows. -/
theorem solution (μ : Measure (ℝ≥0 × ℝ)) (T S : ℝ≥0)
    (B : Set ℝ) (hB : MeasurableSet B) :
    μ (Ioc 0 (T + S) ×ˢ B) =
      μ (Ioc 0 T ×ˢ B) + μ (Ioc T (T + S) ×ˢ B) := by
  have hTadd : T ≤ T + S := le_add_of_nonneg_right (by positivity)
  have hunion : (Ioc 0 (T + S) ×ˢ B) =
      (Ioc 0 T ×ˢ B) ∪ (Ioc T (T + S) ×ˢ B) := by
    ext p
    constructor
    · rintro ⟨⟨hp0, hpadd⟩, hpB⟩
      by_cases hpT : p.1 ≤ T
      · exact Or.inl ⟨⟨hp0, hpT⟩, hpB⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hpT, hpadd⟩, hpB⟩
    · rintro (⟨⟨hp0, hpT⟩, hpB⟩ | ⟨⟨hpT, hpadd⟩, hpB⟩)
      · exact ⟨⟨hp0, hpT.trans hTadd⟩, hpB⟩
      · have hzero : (0 : ℝ≥0) ≤ T := by positivity
        exact ⟨⟨lt_of_le_of_lt hzero hpT, hpadd⟩, hpB⟩
  have hdis : Disjoint (Ioc 0 T ×ˢ B) (Ioc T (T + S) ×ˢ B) := by
    apply Set.disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge hp.1.2) hq.1.1
  rw [hunion, measure_union hdis (measurableSet_Ioc.prod hB)]
