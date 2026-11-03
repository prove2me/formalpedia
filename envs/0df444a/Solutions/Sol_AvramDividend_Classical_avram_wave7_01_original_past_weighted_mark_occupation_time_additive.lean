-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_past_weighted_mark_occupation_time_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T15:32:16.1302+00:00
-- url     : https://prove2.me/submissions/f7afcb65-b6aa-4af4-989a-f83c483030f4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original past-weighted expected marked-count measure is time-additive. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t u : ℝ≥0) (hst : s ≤ t) (htu : t ≤ u)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ Q : Measure (ℝ≥0 × ℝ),
      (∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        Q C = (∫⁻ ω in A, ((Measure.count.restrict {v : ℝ≥0 |
          0 < v ∧ X.X v ω -
            Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
          (fun v : ℝ≥0 => (v,
            X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) C ∂P)) ∧
      Q (Ioc s u ×ˢ B) =
        Q (Ioc s t ×ˢ B) + Q (Ioc t u ×ˢ B) := by
  obtain ⟨Q, hQ⟩ :=
    avram_wave6_01_original_past_expected_time_mark_occupation_measure
      X s A hA
  refine ⟨Q, hQ, ?_⟩
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
  rw [hUnion]
  exact measure_union hDisj (measurableSet_Ioc.prod hB)
