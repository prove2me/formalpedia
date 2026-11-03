-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_intrinsic_arbitrary_mark_adjacent_interval_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:27:06.980207+00:00
-- url     : https://prove2.me/submissions/5e8d06ae-ea85-46e7-8e6b-f9eb70f6eb45

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Literal original-source marked jump count is additive on adjacent intervals. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {v : ℝ≥0 |
        0 < v ∧ X.X v ω -
          Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
        (fun v : ℝ≥0 => (v,
          X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
     NX (Ioc s u ×ˢ B) =
       NX (Ioc s t ×ˢ B) + NX (Ioc t u ×ˢ B)) := by
  classical
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v)))
  change NX (Ioc s u ×ˢ B) =
    NX (Ioc s t ×ˢ B) + NX (Ioc t u ×ˢ B)
  have hUnion :
      Ioc s u ×ˢ B = (Ioc s t ×ˢ B) ∪ (Ioc t u ×ˢ B) := by
    ext p
    rcases p with ⟨v, z⟩
    simp only [mem_prod, mem_Ioc, mem_union]
    constructor
    · rintro ⟨⟨hsv, hvu⟩, hz⟩
      by_cases hvt : v ≤ t
      · exact Or.inl ⟨⟨hsv, hvt⟩, hz⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hvt, hvu⟩, hz⟩
    · rintro (⟨⟨hsv, hvt⟩, hz⟩ | ⟨⟨htv, hvu⟩, hz⟩)
      · exact ⟨⟨hsv, hvt.trans htu⟩, hz⟩
      · exact ⟨⟨lt_of_le_of_lt hst htv, hvu⟩, hz⟩
  have hDisj : Disjoint (Ioc s t ×ˢ B) (Ioc t u ×ˢ B) := by
    apply Set.disjoint_left.mpr
    rintro p hpA hpB
    exact (not_lt_of_ge hpA.1.2) hpB.1.1
  have hMeas : MeasurableSet (Ioc t u ×ˢ B) :=
    measurableSet_Ioc.prod hB
  rw [hUnion]
  exact measure_union hDisj hMeas
