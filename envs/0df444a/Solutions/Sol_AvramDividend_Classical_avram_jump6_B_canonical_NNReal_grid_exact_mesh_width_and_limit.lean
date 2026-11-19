-- Prove2me | solution 1 for AvramDividend.Classical.avram_jump6_B_canonical_NNReal_grid_exact_mesh_width_and_limit
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-18T20:14:52.899208+00:00
-- url     : https://prove2.me/submissions/2aa4a9f7-0ef7-475d-9940-810c338e7370

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Topology
open scoped NNReal ENNReal Topology
noncomputable section

theorem solution :
    let u : ℕ → ℕ → ℝ≥0 := fun j i =>
      (i : ℝ≥0) / ((j + 1 : ℕ) : ℝ≥0)
    (∀ j i, (u j (i + 1) : ℝ) - (u j i : ℝ) =
       (1 : ℝ) / ((j : ℝ) + 1)) ∧
    Tendsto (fun j : ℕ => (1 : ℝ) / ((j : ℝ) + 1))
      atTop (𝓝 (0 : ℝ)) := by
  dsimp only
  constructor
  · intro j i
    simp only [NNReal.coe_div, Nat.cast_add, Nat.cast_one]
    have hj : ((j : ℝ) + 1) ≠ 0 := by positivity
    push_cast
    field_simp
    ring
  · exact tendsto_one_div_add_atTop_nhds_zero_nat
