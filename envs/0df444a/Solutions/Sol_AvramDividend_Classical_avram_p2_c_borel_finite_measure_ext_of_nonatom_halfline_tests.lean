-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_finite_measure_ext_of_nonatom_halfline_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:24:09.701195+00:00
-- url     : https://prove2.me/submissions/1ef2cc01-88ca-45a8-bb34-96c4033d045a

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_measure_ext_of_decreasing_halfline_tests

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Finite real Borel measures are determined by non-atomic half-line tests. -/
theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hTests : ∀ a : ℝ, ν {a} = 0 → μ (Iic a) = ν (Iic a)) :
    μ = ν := by
  let atoms : Set ℝ := {a | 0 < ν {a}}
  have hCountable : atoms.Countable := by
    simpa [atoms] using
      (Measure.countable_meas_level_set_pos (μ := ν) (g := id) measurable_id)
  have hDense : Dense atomsᶜ := hCountable.dense_compl ℝ
  apply AvramDividend.Classical.avram_p2_c_borel_measure_ext_of_decreasing_halfline_tests μ ν
  intro a
  obtain ⟨q, hStrict, hMem, hLim⟩ :=
    hDense.exists_seq_strictAnti_tendsto a
  refine ⟨q, hStrict.antitone, hLim, ?_, ?_⟩
  · intro n
    exact le_of_lt (hMem n).1
  · intro n
    have hNotPos : ¬ (0 : ℝ≥0∞) < ν {q n} := by
      simpa [atoms] using (hMem n).2
    have hZero : ν {q n} = 0 :=
      le_antisymm (le_of_not_gt hNotPos) bot_le
    exact hTests (q n) hZero
