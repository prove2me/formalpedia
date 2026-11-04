-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_a_zero_rate_selected_cell_indices_eventually_distinct
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:38:22.740696+00:00
-- url     : https://prove2.me/submissions/b0f06f38-3a55-4975-8058-481ebbb51d0d

import Mathlib
-- Preserve Mathlib: targeted auto import caused Filter/NNReal and parser CEs 24796.

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Filter Topology
open scoped NNReal

/-- Two distinct jump times occupy distinct shrinking selected cells eventually,
provided the selected right endpoints converge to the genuine times. -/
theorem solution
    (u v : ℝ≥0) (huv : u ≠ v) (i j : ℕ → ℕ) (w : ℕ → ℝ≥0)
    (hi : Tendsto (fun n : ℕ =>
      ((i n + 1 : ℕ) : ℝ≥0) * w n) atTop (𝓝 u))
    (hj : Tendsto (fun n : ℕ =>
      ((j n + 1 : ℕ) : ℝ≥0) * w n) atTop (𝓝 v)) :
    ∀ᶠ n : ℕ in atTop, i n ≠ j n := by
  have hpair : Tendsto (fun n : ℕ =>
      (((i n + 1 : ℕ) : ℝ≥0) * w n,
        ((j n + 1 : ℕ) : ℝ≥0) * w n))
      atTop (𝓝 (u, v)) := by
    simpa only [nhds_prod_eq] using hi.prodMk hj
  have hopen : IsOpen {p : ℝ≥0 × ℝ≥0 | p.1 ≠ p.2} :=
    isOpen_ne_fun continuous_fst continuous_snd
  have hevent : ∀ᶠ n : ℕ in atTop,
      ((i n + 1 : ℕ) : ℝ≥0) * w n ≠
        ((j n + 1 : ℕ) : ℝ≥0) * w n := by
    exact hpair.eventually (hopen.mem_nhds huv)
  filter_upwards [hevent] with n hne heq
  exact hne (by rw [heq])
