-- Prove2me | solution 1 for DerivativeChainClusterAnchor.ordinaryRow_eval_zero_of_exact_cluster
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:21:33.862168+00:00
-- url     : https://prove2.me/submissions/0009f675-9cc2-4a0c-a194-ebdd1fb08a11

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
import Theorems.Thm_DerivativeChainClusterAnchor_ordinaryRow_subset_product
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
open Polynomial Finset
namespace DerivativeChainClusterAnchor
noncomputable section

-- Slot indices retain coincident root values as separate factors.
-- The proof extends Mathlib's iterate_derivative_prod_X_sub_C to a noninjective root map.








theorem ordinaryRow_eval_subset_product {n m : ℕ} (a : Fin n → ℂ) (hm : m ≤ n) (c : ℂ) :
    (ordinaryRow a m).eval c = (n.choose m:ℂ)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, ∏ i ∈ S, (c-a i) := by
  rw [ordinaryRow_subset_product a hm]
  simp only [eval_mul,eval_C,eval_finsetSum,eval_prod,eval_sub,eval_X]

end
end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset Polynomial
open DerivativeChainClusterAnchor






theorem solution {n m r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hm : m ≤ n) (hO : O.card ≤ r) (hrm : r < m)
    (hnear : ∀ i, i ∉ O → a i=c) :
    (_root_.DerivativeChainClusterAnchor.ordinaryRow a m).eval c=0 := by
  classical
  rw [_root_.DerivativeChainClusterAnchor.ordinaryRow_eval_subset_product a hm c]
  have hz : ∀ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
      (∏ i ∈ S, (c-a i))=0 := by
    intro S hS
    have hnot : ¬S ⊆ O := by
      intro hsub
      have hc := Finset.card_le_card hsub
      have hcard : S.card=m := (Finset.mem_powersetCard.mp hS).2
      omega
    obtain ⟨i,hiS,hiO⟩ := Finset.not_subset.mp hnot
    exact Finset.prod_eq_zero hiS (by rw [hnear i hiO,sub_self])
  rw [Finset.sum_eq_zero hz,mul_zero]
