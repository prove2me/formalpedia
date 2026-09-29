-- Prove2me | solution 1 for BlockCycleRotation.sum_fst_eq_sum_snd
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:05:30.610986+00:00
-- url     : https://prove2.me/submissions/a76a816e-b58c-4351-8e58-5f50b8ea0bb3

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Mathlib

open Real Finset

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

theorem mem_quadruples {n a b a' b' : ℕ} :
    (a, b, a', b') ∈ quadruples n ↔
      (a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b' ∧ b' < b
        ∧ Nat.gcd a a' = 1 ∧ Nat.gcd b b' = 1 ∧ n = a * b + a' * b' := by
  simp [quadruples, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- The quadruple set is symmetric under swapping the two halves. -/
theorem mem_quadruples_swap {n a b a' b' : ℕ} (h : (a, b, a', b') ∈ quadruples n) :
    (b, a, b', a') ∈ quadruples n := by
  rw [mem_quadruples] at h ⊢
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9, h10, h11⟩ := h
  exact ⟨⟨h2, h1, h4, h3⟩, h7, h8, h5, h6, h10, h9, by rw [h11]; ring⟩

end BlockCycleRotation

open BlockCycleRotation in
/-- **Summing `a` over the quadruples is the same as summing `b`.**

The paper uses this to symmetrise; it is the involution swapping the two
halves of the quadruple. -/
theorem solution (n : ℕ) :
    ∑ q ∈ quadruples n, q.1 = ∑ q ∈ quadruples n, q.2.1:= by
  refine Finset.sum_bij'
    (i := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1))
    (j := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, a', b'⟩ hq
    exact mem_quadruples_swap hq
  · rintro ⟨a, b, a', b'⟩ hq
    exact mem_quadruples_swap hq
  · rintro ⟨a, b, a', b'⟩ _
    rfl
  · rintro ⟨a, b, a', b'⟩ _
    rfl
  · rintro ⟨a, b, a', b'⟩ _
    rfl
