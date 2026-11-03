-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_measure_arbitrary_set_negative_support
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T14:46:13.029806+00:00
-- url     : https://prove2.me/submissions/7223c52b-45ba-4968-aaa6-67bfdb367f91

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (S : Set (ℝ≥0 × ℝ)) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      S =
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (S ∩ (Set.univ ×ˢ Iio (0 : ℝ))) := by
  let μ : Measure (ℝ≥0 × ℝ) :=
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u))
  have hzero : μ (Set.univ ×ˢ Ici (0 : ℝ)) = 0 := by
    exact avram_wave5_01_actual_intrinsic_marked_measure_global_nonnegative_support_zero X ω
  have hcover :
      S ⊆ (S ∩ (Set.univ ×ˢ Iio (0 : ℝ))) ∪
        (Set.univ ×ˢ Ici (0 : ℝ)) := by
    intro p hp
    rcases p with ⟨u, z⟩
    by_cases hz : z < 0
    · exact Or.inl ⟨hp, by simp [hz]⟩
    · exact Or.inr (by simp [le_of_not_gt hz])
  change μ S = μ (S ∩ (Set.univ ×ˢ Iio (0 : ℝ)))
  apply le_antisymm
  · calc
      μ S ≤ μ ((S ∩ (Set.univ ×ˢ Iio (0 : ℝ))) ∪
        (Set.univ ×ˢ Ici (0 : ℝ))) := measure_mono hcover
      _ ≤ μ (S ∩ (Set.univ ×ˢ Iio (0 : ℝ))) +
          μ (Set.univ ×ˢ Ici (0 : ℝ)) := measure_union_le _ _
      _ = μ (S ∩ (Set.univ ×ˢ Iio (0 : ℝ))) := by rw [hzero, add_zero]
  · exact measure_mono inter_subset_left
