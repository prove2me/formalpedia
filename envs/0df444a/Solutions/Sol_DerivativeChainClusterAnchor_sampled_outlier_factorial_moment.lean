-- Prove2me | solution 1 for DerivativeChainClusterAnchor.sampled_outlier_factorial_moment
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:15:43.701983+00:00
-- url     : https://prove2.me/submissions/0bbbaf5f-aa5e-4805-827b-ed555ead678a

import Mathlib
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
open Finset
namespace DerivativeChainClusterAnchor
noncomputable section



theorem inclusion_factorial_ratio (n m j : ℕ) (hm : m ≤ n) (hj : j ≤ m) :
    ((n-j).choose (m-j):ℝ)/(n.choose m:ℝ) =
      (m.descFactorial j:ℝ)/(n.descFactorial j:ℝ) := by
  have hn : (n.choose m:ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero hm
  have hnj : (n.choose j:ℝ) ≠ 0 := by exact_mod_cast Nat.choose_ne_zero (hj.trans hm)
  have hf : (j.factorial:ℝ) ≠ 0 := by exact_mod_cast Nat.factorial_ne_zero j
  have hmul : (n.choose m:ℝ)*(m.choose j:ℝ) =
      (n.choose j:ℝ)*((n-j).choose (m-j):ℝ) := by
    exact_mod_cast (Nat.choose_mul (n := n) hj)
  simp only [Nat.descFactorial_eq_factorial_mul_choose,Nat.cast_mul]
  field_simp
  nlinarith only [hmul]

theorem subset_inclusion_moment_count {n : ℕ} (O : Finset (Fin n)) (m j : ℕ)
    (hjm : j ≤ m) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, (S ∩ O).card.choose j) =
      O.card.choose j * (n-j).choose (m-j) := by
  classical
  have hinner (S : Finset (Fin n)) : (S ∩ O).card.choose j =
      ∑ T ∈ O.powersetCard j, if T ⊆ S then 1 else 0 := by
    have hf : (O.powersetCard j).filter (· ⊆ S) = (S ∩ O).powersetCard j := by
      ext T
      simp only [Finset.mem_filter,Finset.mem_powersetCard,Finset.subset_inter_iff]
      tauto
    rw [← Finset.card_powersetCard, ← hf]
    simp
  simp_rw [hinner]
  rw [Finset.sum_comm]
  have hcount (T : Finset (Fin n)) (hT : T ∈ O.powersetCard j) :
      (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, if T ⊆ S then 1 else 0) =
        (n-j).choose (m-j) := by
    have hc := Finset.card_filter_powersetCard_subset T (Finset.univ : Finset (Fin n)) m
      (Finset.subset_univ T) (by simpa only [(Finset.mem_powersetCard.mp hT).2] using hjm)
    simpa [Finset.card_univ,Fintype.card_fin,(Finset.mem_powersetCard.mp hT).2,
      Finset.sum_boole] using hc
  rw [Finset.sum_congr rfl hcount]
  simp [Finset.card_powersetCard]



end
end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset
open DerivativeChainClusterAnchor








theorem solution {n : ℕ} (O : Finset (Fin n)) (m j : ℕ)
    (hm : m ≤ n) (hj : j ≤ n) :
    (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, ((S ∩ O).card.choose j:ℝ)) /
        (n.choose m:ℝ) =
      (O.card.choose j:ℝ)*(m.descFactorial j:ℝ)/(n.descFactorial j:ℝ) := by
  classical
  by_cases hjm : j ≤ m
  · have h := _root_.DerivativeChainClusterAnchor.subset_inclusion_moment_count O m j hjm
    have hcast : (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        ((S ∩ O).card.choose j:ℝ)) = (O.card.choose j:ℝ)*((n-j).choose (m-j):ℝ) := by
      exact_mod_cast h
    rw [hcast,mul_div_assoc,_root_.DerivativeChainClusterAnchor.inclusion_factorial_ratio n m j hm hjm]
    ring
  · have hz : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        (S ∩ O).card.choose j=0 := by
      intro S hS
      apply Nat.choose_eq_zero_of_lt
      have hc : S.card=m := (Finset.mem_powersetCard.mp hS).2
      have hle := Finset.card_le_card (Finset.inter_subset_left (s₁ := S) (s₂ := O))
      omega
    have hsum : (∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        ((S ∩ O).card.choose j:ℝ))=0 := by
      apply Finset.sum_eq_zero
      intro S hS
      rw [hz S hS,Nat.cast_zero]
    rw [hsum,zero_div,Nat.descFactorial_eq_zero_iff_lt.mpr (by omega : m < j),
      Nat.cast_zero,mul_zero,zero_div]
