-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_time_rectangle_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:34:24.482806+00:00
-- url     : https://prove2.me/submissions/2d019dd6-d8d5-44f5-92d9-78017555c8af

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped NNReal ENNReal

/-- Adjacent time rectangles split the mass of any marked measure. -/
theorem solution
    (μ : Measure (ℝ≥0 × ℝ))
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (B : Set ℝ) (hB : MeasurableSet B) :
    μ (Ioc s u ×ˢ B) =
      μ (Ioc s t ×ˢ B) + μ (Ioc t u ×ˢ B) := by
  have hSplit :
      Ioc s u ×ˢ B = (Ioc s t ×ˢ B) ∪ (Ioc t u ×ˢ B) := by
    ext x
    simp only [mem_prod, mem_Ioc, mem_union]
    constructor
    · rintro ⟨⟨hxs, hxu⟩, hxB⟩
      by_cases hxt : x.1 ≤ t
      · exact Or.inl ⟨⟨hxs, hxt⟩, hxB⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hxt, hxu⟩, hxB⟩
    · rintro (hl | hr)
      · exact ⟨⟨hl.1.1, le_trans hl.1.2 htu⟩, hl.2⟩
      · exact ⟨⟨lt_of_le_of_lt hst hr.1.1, hr.1.2⟩, hr.2⟩
  have hDisj : Disjoint (Ioc s t ×ˢ B) (Ioc t u ×ˢ B) := by
    apply Set.disjoint_left.mpr
    intro x hx1 hx2
    exact (not_lt_of_ge hx1.1.2) hx2.1.1
  rw [hSplit]
  exact measure_union hDisj (measurableSet_Ioc.prod hB)
