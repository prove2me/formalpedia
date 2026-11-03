-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_06_original_intrinsic_negative_band_void_split_adjacent_horizons
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:20:47.565864+00:00
-- url     : https://prove2.me/submissions/63b04a23-b92f-4227-920a-75ca1ada46c5

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
    (ω : Ω) (T S : ℝ≥0) (n : ℕ) :
    (let NX : Measure (ℝ≥0 × ℝ) :=
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
     let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
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
  let B : Set ℝ := Iic (-(1 / ((n : ℝ) + 1)))
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
