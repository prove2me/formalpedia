-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a427_dyadic_square_grid_sup_monotone
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-14T23:52:31.058438+00:00
-- url     : https://prove2.me/submissions/311aca08-da00-4f39-bd6a-6df5189c77ca

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} (M : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) (ω : Ω) :
    Monotone (fun k : ℕ =>
      (Finset.range (2^k + 1)).sup' (by simp)
        (fun i => (M ((i : ℝ≥0) * T / (2^k : ℝ≥0)) ω)^2)) := by
  classical
  apply monotone_nat_of_le_succ
  intro k
  apply Finset.sup'_le
  intro i hi
  have hiN : i ≤ 2 ^ k := Nat.le_of_lt_succ (Finset.mem_range.mp hi)
  have hmem : 2 * i ∈ Finset.range (2 ^ (k + 1) + 1) := by
    apply Finset.mem_range.mpr
    rw [pow_succ]
    omega
  have htimes :
      (i : ℝ≥0) * T / (2 ^ k : ℝ≥0) =
      ((2 * i : ℕ) : ℝ≥0) * T / (2 ^ (k + 1) : ℝ≥0) := by
    have hk : (2 : ℝ≥0) ^ k ≠ 0 := pow_ne_zero _ (by norm_num)
    rw [pow_succ]
    push_cast
    field_simp [hk]
  rw [htimes]
  exact Finset.le_sup' (s := Finset.range (2 ^ (k + 1) + 1))
    (f := fun (j : ℕ) =>
    (M ((j : ℝ≥0) * T / (2 ^ (k + 1) : ℝ≥0)) ω)^2) hmem
