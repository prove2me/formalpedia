-- Prove2me | solution 1 for AvramDividend.Classical.avram_a118_original_arbitrary_Borel_mark_void_split_adjacent_horizons_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T19:23:44.614514+00:00
-- url     : https://prove2.me/submissions/52e9e430-55bf-47db-b4a1-e735e2a02523

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Source-path factorisation of a negative-band void event across adjacent horizons. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (T S : ℝ≥0) (B : Set ℝ) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     NX (Ioc 0 (T + S) ×ˢ B) = 0 ↔
       NX (Ioc 0 T ×ˢ B) = 0 ∧
       NX (Ioc T (T + S) ×ˢ B) = 0) := by
  classical
  let NX : Measure (ℝ≥0 × ℝ) :=
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
  change NX (Ioc 0 (T + S) ×ˢ B) = 0 ↔
    NX (Ioc 0 T ×ˢ B) = 0 ∧ NX (Ioc T (T + S) ×ˢ B) = 0
  have hUnion :
      Ioc (0 : ℝ≥0) (T + S) ×ˢ B =
        (Ioc 0 T ×ˢ B) ∪ (Ioc T (T + S) ×ˢ B) := by
    ext p
    rcases p with ⟨t, z⟩
    simp only [mem_prod, mem_Ioc, mem_union]
    constructor
    · rintro ⟨⟨h0, hTS⟩, hz⟩
      by_cases hT : t ≤ T
      · exact Or.inl ⟨⟨h0, hT⟩, hz⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hT, hTS⟩, hz⟩
    · rintro (⟨⟨h0, hT⟩, hz⟩ | ⟨⟨hT, hTS⟩, hz⟩)
      · exact ⟨⟨h0, hT.trans (le_add_of_nonneg_right (by positivity))⟩, hz⟩
      · exact ⟨⟨lt_of_le_of_lt (by positivity) hT, hTS⟩, hz⟩
  rw [hUnion]
  constructor
  · intro h
    constructor
    · have hA : NX (Ioc 0 T ×ˢ B) ≤
          NX ((Ioc 0 T ×ˢ B) ∪ (Ioc T (T + S) ×ˢ B)) :=
        measure_mono Set.subset_union_left
      exact le_antisymm (by simpa [h] using hA) bot_le
    · have hB : NX (Ioc T (T + S) ×ˢ B) ≤
          NX ((Ioc 0 T ×ˢ B) ∪ (Ioc T (T + S) ×ˢ B)) :=
        measure_mono Set.subset_union_right
      exact le_antisymm (by simpa [h] using hB) bot_le
  · rintro ⟨hA, hB⟩
    apply le_antisymm
    · calc
        NX ((Ioc 0 T ×ˢ B) ∪ (Ioc T (T + S) ×ˢ B)) ≤
            NX (Ioc 0 T ×ˢ B) + NX (Ioc T (T + S) ×ˢ B) :=
          measure_union_le _ _
        _ = 0 := by simp [hA, hB]
    · exact bot_le
