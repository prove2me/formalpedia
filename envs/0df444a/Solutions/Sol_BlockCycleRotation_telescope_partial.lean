-- Prove2me | solution 1 for BlockCycleRotation.telescope_partial
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:36:48.224529+00:00
-- url     : https://prove2.me/submissions/b7c0f1e9-97e7-468a-891d-6b7d716951b2

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset Filter Topology

namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

@[simp]
theorem norm_e (θ : ℝ) : ‖e θ‖ = 1 := Complex.norm_exp_ofReal_mul_I θ

@[simp]
theorem norm_e_pow (θ : ℝ) (n : ℕ) : ‖e θ ^ n‖ = 1 := by
  rw [norm_pow, norm_e, one_pow]

@[simp]
theorem e_zero : e 0 = 1 := by simp [e]

@[simp] theorem K_nil : K [] = 1 := rfl

@[simp] theorem K_singleton (c : ℕ) : K [c] = c := rfl

@[simp] theorem cf_zero (a : ℕ) : cf a 0 = [] := by rw [cf]; simp

end BlockCycleRotation

open BlockCycleRotation in
/-- The partial sums of the telescoping series. -/
theorem solution (n N : ℕ) (h : n ≤ N) :
    ∑ j ∈ Finset.range N, (1 / ((j : ℝ) + 1) - 1 / ((j : ℝ) + (n : ℝ) + 1))
      = (∑ j ∈ Finset.range n, 1 / ((j : ℝ) + 1))
        - ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1):= by
  have h1 : ∑ j ∈ Finset.range N, 1 / ((j : ℝ) + (n : ℝ) + 1)
      = ∑ j ∈ Finset.Ico n (N + n), 1 / ((j : ℝ) + 1) := by
    rw [Finset.sum_Ico_eq_sum_range]
    simp only [Nat.add_sub_cancel]
    refine Finset.sum_congr rfl fun j _ => ?_
    push_cast
    ring_nf
  rw [Finset.sum_sub_distrib, h1, Finset.range_eq_Ico, Finset.range_eq_Ico]
  have s1 : (∑ j ∈ Finset.Ico 0 n, 1 / ((j : ℝ) + 1))
      + ∑ j ∈ Finset.Ico n N, 1 / ((j : ℝ) + 1)
      = ∑ j ∈ Finset.Ico 0 N, 1 / ((j : ℝ) + 1) :=
    Finset.sum_Ico_consecutive _ (Nat.zero_le n) h
  have s2 : (∑ j ∈ Finset.Ico n N, 1 / ((j : ℝ) + 1))
      + ∑ j ∈ Finset.Ico N (N + n), 1 / ((j : ℝ) + 1)
      = ∑ j ∈ Finset.Ico n (N + n), 1 / ((j : ℝ) + 1) :=
    Finset.sum_Ico_consecutive _ h (by omega)
  linarith
