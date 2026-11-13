-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb49_original_real_toNNReal_uniform_physical_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-12T21:12:20.959729+00:00
-- url     : https://prove2.me/submissions/1be93b86-af05-4c43-8ab2-52d3229a9637

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Classical MeasureTheory Set Filter
open scoped NNReal Topology
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) :
    let u : ℕ → ℕ → ℝ≥0 := fun n i =>
      Real.toNNReal (T * (i : ℝ) / ((n : ℝ) + 2))
    (∀ n, u n 0 = 0 ∧
      ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
    (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
    (∀ n i, (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2)) := by
  intro u
  have hco (n i : ℕ) :
      (u n i : ℝ) = T * (i : ℝ) / ((n : ℝ) + 2) := by
    have hp : 0 ≤ T * (i : ℝ) / ((n : ℝ) + 2) := by positivity
    exact Real.coe_toNNReal _ hp
  refine ⟨?_, ?_, hco⟩
  · intro n
    constructor
    · simp [u]
    · rw [hco n (n + 1)]
      have hd : ((n : ℝ) + 2) ≠ 0 := by positivity
      push_cast
      field_simp [hd]
      ring
  · intro n i hi
    apply NNReal.coe_le_coe.mp
    rw [hco n i, hco n (i + 1)]
    have hc : (i : ℝ) ≤ ((i + 1 : ℕ) : ℝ) := by exact_mod_cast Nat.le_succ i
    have ht : T * (i : ℝ) ≤ T * ((i + 1 : ℕ) : ℝ) :=
      mul_le_mul_of_nonneg_left hc (le_of_lt hT)
    exact div_le_div_of_nonneg_right ht (by positivity)
