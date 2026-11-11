-- Prove2me | solution 1 for AvramDividend.Classical.avram_a06_uniform_negative_mark_isLevyMeasure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-10T17:33:27.36499+00:00
-- url     : https://prove2.me/submissions/c7dd3061-5567-4c74-a112-79ee7c7862bf

import Mathlib
import Definitions.Def_LeanLevy_Levy_LevyMeasure
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_measure_facts
import Theorems.Thm_AvramDividend_Classical_avram_a06_uniform_negative_mark_bv_moments
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ProbabilityTheory Set
open scoped NNReal ENNReal
noncomputable section

/-- The explicit uniform-negative jump law is a genuine Lévy measure. -/
theorem solution : ProbabilityTheory.IsLevyMeasure
      ((volume : Measure ℝ).restrict (Ioo (-1 : ℝ) 0)) := by
  have hfacts := AvramDividend.Classical.avram_a06_uniform_negative_mark_measure_facts
  have hmom := AvramDividend.Classical.avram_a06_uniform_negative_mark_bv_moments
  refine ⟨?_, hmom.1⟩
  exact hfacts.2.2.2.2 (by simp)