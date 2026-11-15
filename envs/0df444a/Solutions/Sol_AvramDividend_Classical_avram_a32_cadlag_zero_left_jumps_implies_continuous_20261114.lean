-- Prove2me | solution 1 for AvramDividend.Classical.avram_a32_cadlag_zero_left_jumps_implies_continuous_20261114
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T09:01:39.481026+00:00
-- url     : https://prove2.me/submissions/7fc40901-1f7f-48eb-b545-242d2ad0ed7c

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (f : ℝ≥0 → ℝ)
    (hRight : ∀ t : ℝ≥0, ContinuousWithinAt f (Ici t) t)
    (hLeft : ∀ t : ℝ≥0, 0 < t →
      Tendsto f (𝓝[<] t) (𝓝 (f t))) :
    ∀ t : ℝ≥0, ContinuousAt f t := by
  intro t
  apply (continuousAt_iff_continuous_left'_right').2
  constructor
  · by_cases ht : 0 < t
    · exact hLeft t ht
    · have ht0 : t = 0 :=
        le_antisymm (le_of_not_gt ht) (show (0 : ℝ≥0) ≤ t from zero_le)
      subst t
      have hEmpty : (Iio (0 : ℝ≥0)) = ∅ := by
        ext u
        simp
      simp [ContinuousWithinAt, nhdsWithin, hEmpty]
  · exact (hRight t).mono (by
      intro u hu
      exact Set.mem_Ici.mpr (le_of_lt (Set.mem_Ioi.mp hu)))
