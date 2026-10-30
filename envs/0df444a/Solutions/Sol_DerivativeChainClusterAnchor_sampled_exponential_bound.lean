-- Prove2me | solution 1 for DerivativeChainClusterAnchor.sampled_exponential_bound
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:17:13.920081+00:00
-- url     : https://prove2.me/submissions/0e31cd59-6b6c-48f0-b4d1-f557df96451e

import Mathlib
import Theorems.Thm_DerivativeChainClusterAnchor_factorial_ratio_bound
import Theorems.Thm_DerivativeChainClusterAnchor_sampled_outlier_factorial_moment
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainExtremal
end DerivativeChainExtremal
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset Polynomial
namespace DerivativeChainClusterAnchor
noncomputable section

theorem binomial_expansion_up_to (N q : ℕ) (hq : q ≤ N) (t : ℝ) :
    (1+t)^q = ∑ j ∈ Finset.range (N+1), (q.choose j:ℝ)*t^j := by
  have hbase : (1+t)^q = ∑ j ∈ Finset.range (q+1), (q.choose j:ℝ)*t^j := by
    simpa only [one_pow,mul_one,add_comm t 1,mul_comm] using (add_pow t 1 q)
  rw [hbase]
  apply Finset.sum_subset (Finset.range_mono (by omega : q+1 ≤ N+1))
  intro j _ hj
  have hqj : q < j := by simp only [Finset.mem_range] at hj; omega
  rw [Nat.choose_eq_zero_of_lt hqj,Nat.cast_zero,zero_mul]

theorem sampled_exponential_expansion {n : ℕ} (O : Finset (Fin n)) (m : ℕ) (hm : m ≤ n)
    (t : ℝ) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, (1+t)^(S ∩ O).card) /
        (n.choose m:ℝ) =
      ∑ j ∈ Finset.range (O.card+1),
        (O.card.choose j:ℝ)*((m.descFactorial j:ℝ)/(n.descFactorial j:ℝ))*t^j := by
  have hcard : O.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ O)
  have hinner (S : Finset (Fin n)) : (1+t)^(S ∩ O).card =
      ∑ j ∈ Finset.range (O.card+1), ((S ∩ O).card.choose j:ℝ)*t^j :=
    binomial_expansion_up_to O.card (S ∩ O).card (Finset.card_le_card Finset.inter_subset_right) t
  simp_rw [hinner]
  rw [Finset.sum_comm,Finset.sum_div]
  apply Finset.sum_congr rfl
  intro j hj
  have hjn : j ≤ n := by have h := Finset.mem_range.mp hj; omega
  rw [← Finset.sum_mul,mul_div_right_comm,sampled_outlier_factorial_moment O m j hm hjn]
  ring





end
end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset Polynomial
open DerivativeChainClusterAnchor






theorem solution {n : ℕ} (O : Finset (Fin n)) (m : ℕ) (hn : 0 < n)
    (hm : m ≤ n) (t : ℝ) (ht : 0 ≤ t) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, (1+t)^(S ∩ O).card) /
        (n.choose m:ℝ) ≤ (1+(m:ℝ)/(n:ℝ)*t)^O.card := by
  rw [_root_.DerivativeChainClusterAnchor.sampled_exponential_expansion O m hm t]
  have hcard : O.card ≤ n := by simpa using Finset.card_le_card (Finset.subset_univ O)
  calc
    _ ≤ ∑ j ∈ Finset.range (O.card+1),
        (O.card.choose j:ℝ)*((m:ℝ)/(n:ℝ))^j*t^j := by
      apply Finset.sum_le_sum
      intro j hj
      have hjn : j ≤ n := by have h := Finset.mem_range.mp hj; omega
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left (_root_.DerivativeChainClusterAnchor.factorial_ratio_bound n m j hn hm hjn) (Nat.cast_nonneg _))
        (pow_nonneg ht _)
    _ = _ := by
      simpa only [one_pow,mul_one,mul_pow,add_comm,
        mul_comm,mul_assoc,mul_left_comm] using (add_pow ((m:ℝ)/(n:ℝ)*t) 1 O.card).symm
