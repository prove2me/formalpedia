-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_intrinsic_jump_count_time_interval_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T01:22:24.297037+00:00
-- url     : https://prove2.me/submissions/8777be13-c6bf-45fd-9765-4943e05d3704

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s u t : ℝ≥0) (hsu : s ≤ u) (hut : u ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s t ×ˢ B) =
      ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc s u ×ˢ B) +
      ((Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))) (Ioc u t ×ˢ B) := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {v : ℝ≥0 |
      0 < v ∧ X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v ≠ 0}).map
      (fun v : ℝ≥0 => (v,
        X.X v ω - Function.leftLim (fun w : ℝ≥0 => X.X w ω) v))
  have hUnion : Ioc s t ×ˢ B =
      (Ioc s u ×ˢ B) ∪ (Ioc u t ×ˢ B) := by
    ext p
    rcases p with ⟨a, b⟩
    constructor
    · rintro ⟨⟨hsa, hat⟩, hb⟩
      by_cases hau : a ≤ u
      · exact Or.inl ⟨⟨hsa, hau⟩, hb⟩
      · exact Or.inr ⟨⟨lt_of_not_ge hau, hat⟩, hb⟩
    · rintro (⟨⟨hsa, hau⟩, hb⟩ | ⟨⟨hua, hat⟩, hb⟩)
      · exact ⟨⟨hsa, le_trans hau hut⟩, hb⟩
      · exact ⟨⟨lt_of_le_of_lt hsu hua, hat⟩, hb⟩
  have hDisjoint : Disjoint (Ioc s u ×ˢ B) (Ioc u t ×ˢ B) := by
    apply Set.disjoint_left.mpr
    intro p hp₁ hp₂
    exact (not_lt_of_ge hp₁.1.2) hp₂.1.1
  have hMeas : MeasurableSet (Ioc u t ×ˢ B) :=
    measurableSet_Ioc.prod hB
  change μ (Ioc s t ×ˢ B) =
    μ (Ioc s u ×ˢ B) + μ (Ioc u t ×ˢ B)
  rw [hUnion]
  exact measure_union hDisjoint hMeas
