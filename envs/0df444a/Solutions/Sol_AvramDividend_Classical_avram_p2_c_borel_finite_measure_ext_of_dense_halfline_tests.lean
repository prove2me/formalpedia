-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_finite_measure_ext_of_dense_halfline_tests
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T12:42:46.548382+00:00
-- url     : https://prove2.me/submissions/a4820084-3cb7-45b8-8437-0425da199692

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_measure_ext_of_decreasing_halfline_tests

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped ENNReal

/-- Finite measures agree globally once they agree on dense lower half-line tests. -/
theorem solution
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (D : Set ℝ) (hDense : Dense D)
    (hTests : ∀ a : ℝ, a ∈ D → μ (Iic a) = ν (Iic a)) :
    μ = ν := by
  apply AvramDividend.Classical.avram_p2_c_borel_measure_ext_of_decreasing_halfline_tests μ ν
  intro a
  obtain ⟨q, hStrict, hMem, hLim⟩ :=
    hDense.exists_seq_strictAnti_tendsto a
  refine ⟨q, hStrict.antitone, hLim, ?_, ?_⟩
  · intro n
    exact le_of_lt (hMem n).1
  · intro n
    exact hTests (q n) (hMem n).2
