-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_grid4_original_strict_prefix_uniform_physical_grid
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-06T08:22:22.877204+00:00
-- url     : https://prove2.me/submissions/18421345-a537-45c6-9f4c-b0e5bbdd2495

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

/-- Original strict T physical cells stay before the horizon by one exact
positive mesh step, preserving the right-payment convention at T. -/
theorem solution
    (T : ℝ) (hT : 0 < T) :
    ∃ u : ℕ → ℕ → ℝ≥0,
      (∀ n, u n 0 = 0) ∧
      (∀ n, ((u n (n + 1) : ℝ) = T - T / ((n : ℝ) + 2))) ∧
      (∀ n i, i < n + 1 → u n i ≤ u n (i + 1)) ∧
      (∀ n i, i < n + 1 →
        (u n (i + 1) : ℝ) - (u n i : ℝ) = T / ((n : ℝ) + 2)) := by
  let t : ℝ≥0 := ⟨T, le_of_lt hT⟩
  refine ⟨(fun n i => (i : ℝ≥0) * (t / ((n : ℝ≥0) + 2))),
    ?_, ?_, ?_, ?_⟩
  · intro n
    simp
  · intro n
    change (((n + 1 : ℕ) : ℝ≥0) * (t / ((n : ℝ≥0) + 2)) : ℝ) =
      T - T / ((n : ℝ) + 2)
    push_cast
    have ht : (t : ℝ) = T := rfl
    rw [ht]
    have hn : (n : ℝ) + 2 ≠ 0 := by positivity
    field_simp
    ring
  · intro n i hi
    dsimp
    gcongr
    exact Nat.le_succ i
  · intro n i hi
    change ((((i + 1 : ℕ) : ℝ≥0) * (t / ((n : ℝ≥0) + 2)) : ℝ) -
      (((i : ℕ) : ℝ≥0) * (t / ((n : ℝ≥0) + 2)) : ℝ)) =
      T / ((n : ℝ) + 2)
    push_cast
    have ht : (t : ℝ) = T := rfl
    rw [ht]
    ring
