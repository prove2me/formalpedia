-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_adjacent_window_counts_add
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:30:37.368187+00:00
-- url     : https://prove2.me/submissions/88b8788e-19e3-43b8-8dd7-b36d8f4b2126

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact additive decomposition of the original intrinsic marked count on
adjacent time windows, valid for infinite activity and infinite counts. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∀ ω : Ω,
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s u ×ˢ B) =
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc s t ×ˢ B) +
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
        (Ioc t u ×ˢ B) := by
  intro ω
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))
  change μ (Ioc s u ×ˢ B) =
    μ (Ioc s t ×ˢ B) + μ (Ioc t u ×ˢ B)
  have hUnion : Ioc s u ×ˢ B =
      (Ioc s t ×ˢ B) ∪ (Ioc t u ×ˢ B) := by
    ext x
    rcases x with ⟨v, z⟩
    simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_union]
    constructor
    · rintro ⟨⟨hsv, hvu⟩, hz⟩
      by_cases hvt : v ≤ t
      · exact Or.inl ⟨⟨hsv, hvt⟩, hz⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hvt, hvu⟩, hz⟩
    · rintro (⟨⟨hsv, hvt⟩, hz⟩ | ⟨⟨htv, hvu⟩, hz⟩)
      · exact ⟨⟨hsv, le_trans hvt htu⟩, hz⟩
      · exact ⟨⟨lt_of_le_of_lt hst htv, hvu⟩, hz⟩
  have hDisj : Disjoint (Ioc s t ×ˢ B) (Ioc t u ×ˢ B) := by
    apply Set.disjoint_left.mpr
    intro x hx hy
    exact (not_lt_of_ge hx.1.2) hy.1.1
  rw [hUnion]
  exact measure_union hDisj (measurableSet_Ioc.prod hB)
