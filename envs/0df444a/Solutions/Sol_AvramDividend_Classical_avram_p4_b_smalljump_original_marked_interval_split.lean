-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_marked_interval_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:20:22.826563+00:00
-- url     : https://prove2.me/submissions/177c5d6d-3a7c-4987-9a3f-a27ccd5a495f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal

/-- Time-rectangle additivity of the genuine intrinsic marked-jump random
measure on the original sample space, with no Poisson surrogate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (s r t : ℝ≥0) (hsr : s ≤ r) (hrt : r ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (let N : Measure (ℝ≥0 × ℝ) :=
      (Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u));
      N (Ioc s t ×ˢ B) = N (Ioc s r ×ˢ B) + N (Ioc r t ×ˢ B)) := by
  let N : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  change N (Ioc s t ×ˢ B) = N (Ioc s r ×ˢ B) + N (Ioc r t ×ˢ B)
  have hUnion :
      (Ioc s t ×ˢ B) = (Ioc s r ×ˢ B) ∪ (Ioc r t ×ˢ B) := by
    ext p
    rcases p with ⟨u, z⟩
    simp only [mem_prod, mem_Ioc, mem_union]
    constructor
    · rintro ⟨⟨hsu, hut⟩, hz⟩
      by_cases hur : u ≤ r
      · exact Or.inl ⟨⟨hsu, hur⟩, hz⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hur, hut⟩, hz⟩
    · rintro (h | h)
      · exact ⟨⟨h.1.1, le_trans h.1.2 hrt⟩, h.2⟩
      · exact ⟨⟨lt_of_le_of_lt hsr h.1.1, h.1.2⟩, h.2⟩
  have hDisj : Disjoint (Ioc s r ×ˢ B) (Ioc r t ×ˢ B) := by
    apply disjoint_left.mpr
    intro p hp hq
    exact (not_lt_of_ge hp.1.2) hq.1.1
  rw [hUnion, measure_union hDisj (measurableSet_Ioc.prod hB)]
