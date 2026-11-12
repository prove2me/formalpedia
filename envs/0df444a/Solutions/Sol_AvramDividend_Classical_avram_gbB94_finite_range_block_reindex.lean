-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB94_finite_range_block_reindex
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T18:48:38.602186+00:00
-- url     : https://prove2.me/submissions/c5c4eace-3be0-4cfe-a806-4bec24f2f932

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open scoped BigOperators

theorem solution
    (M b : ℕ) (hb : 0 < b) (f : ℕ → ℕ → ℝ) :
    (Finset.range M).sum (fun i =>
      (Finset.range b).sum (fun j => f i (i * b + j))) =
    (Finset.range (M * b)).sum (fun r => f (r / b) r) := by
  induction M with
  | zero => simp
  | succ M ih =>
      rw [Finset.sum_range_succ, Nat.succ_mul,
        Finset.sum_range_add, ih]
      congr 1
      apply Finset.sum_congr rfl
      intro j hj
      have hjlt : j < b := Finset.mem_range.mp hj
      have hdiv : (M * b + j) / b = M := by
        rw [Nat.mul_comm M b, Nat.mul_add_div hb M j,
          Nat.div_eq_of_lt hjlt, Nat.add_zero]
      exact congrArg (fun x => f x (M * b + j)) hdiv.symm
