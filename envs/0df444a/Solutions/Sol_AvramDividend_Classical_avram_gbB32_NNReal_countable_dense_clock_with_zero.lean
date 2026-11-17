-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB32_NNReal_countable_dense_clock_with_zero
-- status  : ACCEPTED   (prove)
-- author  : @garyholm
-- created : 2026-11-16T21:07:57.131041+00:00
-- url     : https://prove2.me/submissions/ec145914-b47d-4abd-acc2-65939782d4f9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
theorem AvramDividend.Classical.avram_gbB32_NNReal_countable_dense_clock_with_zero :
    ∃ (S : Set ℝ≥0), S.Countable ∧ Dense S ∧ (0 : ℝ≥0) ∈ S := by
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense ℝ≥0
  exact ⟨insert 0 D, hDc.insert 0, hDd.mono (subset_insert 0 D), mem_insert 0 D⟩

theorem solution :
    ∃ (S : Set ℝ≥0), S.Countable ∧ Dense S ∧ (0 : ℝ≥0) ∈ S :=
  AvramDividend.Classical.avram_gbB32_NNReal_countable_dense_clock_with_zero
