-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva84_original_strict_positive_jump_count_zero_at_initial_clock
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:29:30.860014+00:00
-- url     : https://prove2.me/submissions/056d1945-660f-4cd5-a587-d4513ec3fe49

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    (Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0})
      ({0} : Set ℝ≥0) = 0 := by
  have hd :
      ({0} : Set ℝ≥0) ∩
        {u : ℝ≥0 | 0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0} = ∅ := by
    ext u
    simp only [Set.mem_inter_iff, Set.mem_singleton_iff,
      Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro h
    rcases h with ⟨rfl, hu⟩
    exact (lt_irrefl (0 : ℝ≥0)) hu.1
  rw [Measure.restrict_apply (measurableSet_singleton (0 : ℝ≥0))]
  simp only [hd, measure_empty]
