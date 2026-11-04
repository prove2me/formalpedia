-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_f_weighted_original_intrinsic_Ioc_split_pathwise
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T16:21:32.627931+00:00
-- url     : https://prove2.me/submissions/6ef5b932-ea36-480b-aaf2-58a21f2f7778

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Exact additive splitting of genuine original Lévy intrinsic marked
jump counts, pathwise, across adjacent Ioc clock intervals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s u t : ℝ≥0) (hsu : s ≤ u) (hut : u ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) (ω : Ω) :
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s t ×ˢ B) =
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s u ×ˢ B) +
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc u t ×ˢ B) := by
  let J : Measure (ℝ≥0 × ℝ) := ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
  change J (Ioc s t ×ˢ B) = J (Ioc s u ×ˢ B) + J (Ioc u t ×ˢ B)
  have hsplit : (Ioc s t ×ˢ B) =
      (Ioc s u ×ˢ B) ∪ (Ioc u t ×ˢ B) := by
    ext p
    rcases p with ⟨v, z⟩
    simp only [Set.mem_prod, Set.mem_Ioc, Set.mem_union]
    constructor
    · rintro ⟨⟨hsv, hvt⟩, hz⟩
      by_cases hvu : v ≤ u
      · exact Or.inl ⟨⟨hsv, hvu⟩, hz⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hvu, hvt⟩, hz⟩
    · rintro (⟨⟨hsv, hvu⟩, hz⟩ | ⟨⟨huv, hvt⟩, hz⟩)
      · exact ⟨⟨hsv, le_trans hvu hut⟩, hz⟩
      · exact ⟨⟨lt_of_le_of_lt hsu huv, hvt⟩, hz⟩
  have hdisj : Disjoint (Ioc s u ×ˢ B) (Ioc u t ×ˢ B) := by
    apply Set.disjoint_left.mpr
    intro p hpL hpR
    exact (not_lt_of_ge hpL.1.2) hpR.1.1
  rw [hsplit]
  exact measure_union hdisj (measurableSet_Ioc.prod hB)
