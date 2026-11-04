-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_34dbea70_uniform_halfopen_cell_locator
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T08:29:13.334086+00:00
-- url     : https://prove2.me/submissions/82025ca1-d682-4d85-b563-79651588951d

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology
open scoped NNReal

/-- Every positive time up to T belongs to an open-left, closed-right
uniform mesh cell, including times that coincide with a mesh endpoint. -/
theorem solution
    (T u : ℝ≥0) (hT : 0 < T) (hu : 0 < u) (huT : u ≤ T)
    (n : ℕ) :
    ∃ i : ℕ, i ≤ n ∧
      (i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) < u ∧
      u ≤ ((i + 1 : ℕ) : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) := by
  let q : ℝ≥0 := u * ((n : ℝ≥0) + 1) / T
  let k : ℕ := Nat.ceil q
  have hn : 0 < (n : ℝ≥0) + 1 := by positivity
  have hqpos : 0 < q := by
    dsimp [q]
    exact div_pos (mul_pos hu hn) hT
  have hkpos : 0 < k := (Nat.lt_ceil).2 (by simpa using hqpos)
  have hqle : q ≤ (n : ℝ≥0) + 1 := by
    dsimp [q]
    apply (div_le_iff₀ hT).2
    simpa [mul_comm] using
      (mul_le_mul_of_nonneg_right huT (le_of_lt hn))
  have hkbound : k ≤ n + 1 := by
    apply (Nat.ceil_le).2
    simpa only [Nat.cast_add, Nat.cast_one] using hqle
  let i : ℕ := k - 1
  have hiadd : i + 1 = k := by dsimp [i]; omega
  have hile : i ≤ n := by dsimp [i]; omega
  have hlt : (i : ℝ≥0) < q := by
    apply (Nat.lt_ceil).1
    change i < k
    omega
  have hle : q ≤ (k : ℝ≥0) := Nat.le_ceil q
  refine ⟨i, hile, ?_, ?_⟩
  · have hmul : (i : ℝ≥0) * T < u * ((n : ℝ≥0) + 1) := by
      exact (lt_div_iff₀ hT).1 (by simpa only [q] using hlt)
    calc
      (i : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) =
          ((i : ℝ≥0) * T) / ((n : ℝ≥0) + 1) := by ring
      _ < u := (div_lt_iff₀ hn).2 hmul
  · have hmul : u * ((n : ℝ≥0) + 1) ≤ (k : ℝ≥0) * T := by
      exact (div_le_iff₀ hT).1 (by simpa only [q] using hle)
    rw [hiadd]
    calc
      u ≤ ((k : ℝ≥0) * T) / ((n : ℝ≥0) + 1) :=
        (le_div_iff₀ hn).2 hmul
      _ = (k : ℝ≥0) * (T / ((n : ℝ≥0) + 1)) := by ring
