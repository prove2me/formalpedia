-- Prove2me | solution 1 for BlockCycleRotation.Q_symmetrise
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T11:15:40.445211+00:00
-- url     : https://prove2.me/submissions/23a3a4b3-b359-40c3-a5b7-58b9a2f6d4e3

import Definitions.Def_BlockCycleRotation_Continuant
import Definitions.Def_BlockCycleRotation_Euclid
import Definitions.Def_BlockCycleRotation_ExpSum
import Theorems.Thm_BlockCycleRotation_sum_gt_eq_sum_lt
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

/-- Summing `a` over `quadruplesQ` equals summing `b`. -/
theorem sum_fst_eq_sum_snd_Q (n : ℕ) :
    ∑ q ∈ quadruplesQ n, q.1 = ∑ q ∈ quadruplesQ n, q.2.1 := by
  refine Finset.sum_bij'
    (i := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1))
    (j := fun q _ => (q.2.1, q.1, q.2.2.2, q.2.2.1)) ?_ ?_ ?_ ?_ ?_ <;>
    rintro ⟨a, b, a', b'⟩ hq
  · exact mem_quadruplesQ_swap hq
  · exact mem_quadruplesQ_swap hq
  · rfl
  · rfl
  · rfl

end BlockCycleRotation

open BlockCycleRotation in
/-- **The symmetrisation.**  `Q(n)` splits into the part with `b > a` and the
diagonal. -/
theorem solution (n : ℕ) :
    ∑ q ∈ quadruplesQ n, q.2.1
      = (∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1))
        + ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1:= by
  classical
  have e1 : ((quadruplesQ n).filter (fun q => ¬ q.1 < q.2.1)).filter (fun q => q.2.1 < q.1)
      = (quadruplesQ n).filter (fun q => q.2.1 < q.1) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, -⟩, h⟩
      exact ⟨hq, h⟩
    · rintro ⟨hq, h⟩
      exact ⟨⟨hq, by omega⟩, h⟩
  have e2 : ((quadruplesQ n).filter (fun q => ¬ q.1 < q.2.1)).filter (fun q => ¬ q.2.1 < q.1)
      = (quadruplesQ n).filter (fun q => q.1 = q.2.1) := by
    ext q
    simp only [Finset.mem_filter]
    constructor
    · rintro ⟨⟨hq, h1⟩, h2⟩
      exact ⟨hq, by omega⟩
    · rintro ⟨hq, h⟩
      exact ⟨⟨hq, by omega⟩, by omega⟩
  have hsplit : ∑ q ∈ quadruplesQ n, (q.1 + q.2.1)
      = (∑ q ∈ (quadruplesQ n).filter (fun q => q.1 < q.2.1), (q.1 + q.2.1))
        + ((∑ q ∈ (quadruplesQ n).filter (fun q => q.2.1 < q.1), (q.1 + q.2.1))
          + ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), (q.1 + q.2.1)) := by
    rw [← Finset.sum_filter_add_sum_filter_not (quadruplesQ n) (fun q => q.1 < q.2.1),
      ← Finset.sum_filter_add_sum_filter_not
        ((quadruplesQ n).filter (fun q => ¬ q.1 < q.2.1)) (fun q => q.2.1 < q.1),
      e1, e2]
  have hab : ∑ q ∈ quadruplesQ n, (q.1 + q.2.1) = 2 * ∑ q ∈ quadruplesQ n, q.2.1 := by
    rw [Finset.sum_add_distrib, sum_fst_eq_sum_snd_Q]
    ring
  have hdiag : ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), (q.1 + q.2.1)
      = 2 * ∑ q ∈ (quadruplesQ n).filter (fun q => q.1 = q.2.1), q.1 := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun q hq => ?_
    simp only [Finset.mem_filter] at hq
    omega
  rw [hab, hdiag, sum_gt_eq_sum_lt] at hsplit
  omega
