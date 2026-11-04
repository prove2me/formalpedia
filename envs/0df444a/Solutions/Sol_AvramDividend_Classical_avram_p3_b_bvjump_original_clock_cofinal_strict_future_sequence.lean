-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_b_bvjump_original_clock_cofinal_strict_future_sequence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:38:11.761067+00:00
-- url     : https://prove2.me/submissions/dee7dcc8-9a16-4827-9405-65346f5cb946

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
noncomputable section

theorem solution
    (i : ℝ≥0) :
    ∃ r : ℕ → ℝ≥0,
      Antitone r ∧ (∀ n, i < r n) ∧
        (∀ u : ℝ≥0, i < u → ∃ n, r n < u) := by
  obtain ⟨r, hr, hri, ht⟩ := exists_seq_strictAnti_tendsto i
  refine ⟨r, hr.antitone, hri, ?_⟩
  intro u hiu
  obtain ⟨n, hn⟩ := (ht.eventually (Iio_mem_nhds hiu)).exists
  exact ⟨n, hn⟩
