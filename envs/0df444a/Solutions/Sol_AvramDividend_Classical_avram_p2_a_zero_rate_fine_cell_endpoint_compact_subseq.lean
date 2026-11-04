-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_fine_cell_endpoint_compact_subseq
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T18:31:00.952136+00:00
-- url     : https://prove2.me/submissions/b98ec98a-7811-4cee-8f2b-d3abb07506cf

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- Original nonnegative uniform-grid endpoints lie in a compact interval,
so any chosen sequence has a convergent monotone-index subsequence. -/
theorem solution
    (T : ℝ≥0) (a : ℕ → ℝ≥0) (ha : ∀ n, a n ≤ T) :
    ∃ t : ℝ≥0, t ∈ Icc (0 : ℝ≥0) T ∧
      ∃ φ : ℕ → ℕ, StrictMono φ ∧
        Tendsto (fun n : ℕ => a (φ n)) atTop (𝓝 t) := by
  have hc : IsCompact (Icc (0 : ℝ≥0) T) := isCompact_Icc
  have hm : ∀ n, a n ∈ Icc (0 : ℝ≥0) T := by
    intro n
    exact ⟨zero_le, ha n⟩
  exact hc.tendsto_subseq hm
