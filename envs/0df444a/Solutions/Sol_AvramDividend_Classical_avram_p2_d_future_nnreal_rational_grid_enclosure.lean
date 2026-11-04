-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_nnreal_rational_grid_enclosure
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T19:56:30.923304+00:00
-- url     : https://prove2.me/submissions/9000eb38-02b2-4ed3-b695-6a6487fbcf01

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- Explicit rational mesh enclosure for a nonnegative real horizon, including
zero time and the denominator-one case. -/
theorem solution
    (t : ℝ≥0) (d : ℕ) (hd : 0 < d) :
    ∃ n : ℕ,
      ((n : ℝ≥0) / (d : ℝ≥0)) ≤ t ∧
      t ≤ (((n + 1 : ℕ) : ℝ≥0) / (d : ℝ≥0)) := by
  let n : ℕ := Nat.floor ((d : ℝ≥0) * t)
  have hdpos : (0 : ℝ≥0) < (d : ℝ≥0) := by exact_mod_cast hd
  have hlow : (n : ℝ≥0) ≤ (d : ℝ≥0) * t := by
    dsimp [n]
    exact Nat.floor_le (bot_le : (0 : ℝ≥0) ≤ (d : ℝ≥0) * t)
  have hhigh : (d : ℝ≥0) * t < ((n + 1 : ℕ) : ℝ≥0) := by
    dsimp [n]
    simpa only [Nat.cast_add, Nat.cast_one] using
      (Nat.lt_floor_add_one ((d : ℝ≥0) * t))
  refine ⟨n, ?_, ?_⟩
  · apply (div_le_iff₀ hdpos).2
    simpa [mul_comm] using hlow
  · apply (le_div_iff₀ hdpos).2
    simpa [mul_comm] using hhigh.le
