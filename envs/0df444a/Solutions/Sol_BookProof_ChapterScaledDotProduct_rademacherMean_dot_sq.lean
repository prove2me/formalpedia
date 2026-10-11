-- Prove2me | solution 1 for BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T09:22:45.985056+00:00
-- url     : https://prove2.me/submissions/43d685b2-64dc-4c30-a3fd-0752b3c4ef2c

-- Generated from ChapterScaledDotProduct.lean — solution of BookProof.ChapterScaledDotProduct.rademacherMean_dot_sq
import Mathlib
import Definitions.Def_ChapterScaledDotProduct
import Theorems.Thm_BookProof_ChapterScaledDotProduct_sum_sgn_mul_eq_zero
import Theorems.Thm_BookProof_ChapterScaledDotProduct_sum_sgn_mul_self
import Theorems.Thm_BookProof_ChapterScaledDotProduct_two_pow_ne_zero_prime
import Definitions.Def_ChapterSoftmaxSharpness
open BookProof.ChapterScaledDotProduct



open scoped BigOperators

noncomputable section


open BookProof.ChapterSoftmaxSharpness

variable {d : ℕ}

variable {d : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (k : Fin d → ℝ) :
    rademacherMean (fun x => (dot (signVec x) k) ^ 2) = ∑ i, (k i) ^ 2 := by

  have hexp : ∀ x : (Fin d → Bool), (dot (signVec x) k) ^ 2
      = ∑ i, ∑ j, (sgn (x i) * sgn (x j)) * (k i * k j) := by
    intro x
    rw [sq, dot, Finset.sum_mul_sum]
    exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by
      simp only [signVec]; ring
  have hswap : ∑ x : (Fin d → Bool), (dot (signVec x) k) ^ 2
      = ∑ i, ∑ j, (∑ x : (Fin d → Bool), sgn (x i) * sgn (x j)) * (k i * k j) := by
    rw [Finset.sum_congr rfl fun x (_ : x ∈ Finset.univ) => hexp x]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
  have hinner : ∀ i : Fin d,
      ∑ j, (∑ x : (Fin d → Bool), sgn (x i) * sgn (x j)) * (k i * k j)
        = (2 : ℝ) ^ d * (k i) ^ 2 := by
    intro i
    rw [Finset.sum_eq_single i]
    · rw [sum_sgn_mul_self]; ring
    · intro j _ hj
      rw [sum_sgn_mul_eq_zero (Ne.symm hj), zero_mul]
    · intro hi
      exact absurd (Finset.mem_univ i) hi
  rw [rademacherMean, hswap, Finset.sum_congr rfl fun i (_ : i ∈ Finset.univ) => hinner i,
    ← Finset.mul_sum, mul_comm, mul_div_assoc, div_self two_pow_ne_zero_prime, mul_one]
