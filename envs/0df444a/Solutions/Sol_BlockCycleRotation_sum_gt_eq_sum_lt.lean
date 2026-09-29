-- Prove2me | solution 1 for BlockCycleRotation.sum_gt_eq_sum_lt
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:14:40.114402+00:00
-- url     : https://prove2.me/submissions/406a95a7-5fe8-444d-874d-e6c5a0152755

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

theorem mem_quadruplesQ {n a b a' b' : ℕ} :
    (a, b, a', b') ∈ quadruplesQ n ↔
      (a ≤ n ∧ b ≤ n ∧ a' ≤ n ∧ b' ≤ n) ∧ 1 ≤ a' ∧ a' < a ∧ 1 ≤ b' ∧ b' < b
        ∧ n = a * b + a' * b' := by
  simp [quadruplesQ, Finset.mem_filter, Finset.mem_product, and_assoc]

/-- `quadruplesQ` is symmetric under swapping the two halves. -/
theorem mem_quadruplesQ_swap {n a b a' b' : ℕ} (h : (a, b, a', b') ∈ quadruplesQ n) :
    (b, a, b', a') ∈ quadruplesQ n := by
  rw [mem_quadruplesQ] at h ⊢
  obtain ⟨⟨h1, h2, h3, h4⟩, h5, h6, h7, h8, h9⟩ := h
  exact ⟨⟨h2, h1, h4, h3⟩, h7, h8, h5, h6, by rw [h9]; ring⟩

end BlockCycleRotation

open BlockCycleRotation in
/-- The involution matches the quadruples with `b < a` against those with `b > a`. -/
theorem solution (n : ℕ) :
    ∑ q ∈ (quadruplesQ n).filter (fun q => q.2.1 < q.1), (q.1 + q.2.1)
      = ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1):= by
  refine Finset.sum_bij'
    (i := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1))
    (j := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1)) ?_ ?_ ?_ ?_ ?_
  · rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨mem_quadruplesQ_swap hq.1, hq.2⟩
  · rintro ⟨a, b, a', b'⟩ hq
    simp only [Finset.mem_filter] at hq ⊢
    exact ⟨mem_quadruplesQ_swap hq.1, hq.2⟩
  · rintro ⟨a, b, a', b'⟩ _
    rfl
  · rintro ⟨a, b, a', b'⟩ _
    rfl
  · rintro ⟨a, b, a', b'⟩ _
    exact Nat.add_comm _ _
