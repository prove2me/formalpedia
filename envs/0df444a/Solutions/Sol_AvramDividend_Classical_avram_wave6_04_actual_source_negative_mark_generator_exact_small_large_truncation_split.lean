-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave6_04_actual_source_negative_mark_generator_exact_small_large_truncation_split
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T09:03:13.900432+00:00
-- url     : https://prove2.me/submissions/e831895d-832a-44d1-9a34-d4d2c6ff186f

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Exact original nonlinear negative Lévy Taylor compensation:
small marks (-1,0) subtract the source first derivative, while the
large marks (-∞,-1] carry the full jump, including z=-1. -/
theorem solution
    (w : ℝ → ℝ) (y : ℝ) :
    (∀ z : ℝ, -1 < z → z < 0 →
      SpectrallyNegativeLevy.generatorIntegrand w y z =
        w (y + z) - w y - deriv w y * z) ∧
    (∀ z : ℝ, z ≤ -1 →
      SpectrallyNegativeLevy.generatorIntegrand w y z =
        w (y + z) - w y) := by
  constructor
  · intro z hz1 hz0
    have hmem : z ∈ Ioo (-1 : ℝ) 1 := by
      simp only [Set.mem_Ioo]
      constructor
      · exact hz1
      · linarith
    unfold SpectrallyNegativeLevy.generatorIntegrand
    simp [Set.indicator, hmem]
  · intro z hz1
    have hnot : z ∉ Ioo (-1 : ℝ) 1 := by
      intro hz
      exact (not_lt_of_ge hz1) hz.1
    unfold SpectrallyNegativeLevy.generatorIntegrand
    simp [Set.indicator, hnot]
