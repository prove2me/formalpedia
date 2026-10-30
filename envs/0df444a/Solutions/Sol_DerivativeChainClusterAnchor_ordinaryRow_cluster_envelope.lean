-- Prove2me | solution 1 for DerivativeChainClusterAnchor.ordinaryRow_cluster_envelope
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T23:19:13.415494+00:00
-- url     : https://prove2.me/submissions/90067695-3f49-4f23-aca0-34f406302ce7

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
import Theorems.Thm_DerivativeChainClusterAnchor_ordinaryRow_subset_product
import Theorems.Thm_DerivativeChainClusterAnchor_sampled_exponential_bound
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
namespace DerivativeChainClusterAnchor
noncomputable section







theorem ordinaryRow_eval_norm_subset_bound {n m : ℕ} (a : Fin n → ℂ) (hm : m ≤ n) (c : ℂ) :
    ‖(ordinaryRow a m).eval c‖ ≤ (n.choose m:ℝ)⁻¹ *
      ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m, ∏ i ∈ S, ‖c-a i‖ := by
  rw [ordinaryRow_eval_subset_product a hm c,norm_mul,norm_inv]
  simp only [Complex.norm_natCast]
  apply mul_le_mul_of_nonneg_left _ (by positivity)
  simpa only [norm_prod] using norm_sum_le ((Finset.univ : Finset (Fin n)).powersetCard m)
    (fun S => ∏ i ∈ S, (c-a i))

end
end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset Polynomial
namespace DerivativeChainClusterAnchor
noncomputable section

theorem cluster_subset_norm_product {n : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O S : Finset (Fin n)) (ε D : ℝ) (hε : 0 < ε)
    (hnear : ∀ i, i ∉ O → ‖c-a i‖ ≤ ε) (hfar : ∀ i, i ∈ O → ‖c-a i‖ ≤ D) :
    (∏ i ∈ S, ‖c-a i‖) ≤ ε^S.card*(D/ε)^(S ∩ O).card := by
  classical
  have hpoint (i : Fin n) : ‖c-a i‖ ≤ ε*(if i ∈ O then D/ε else 1) := by
    split_ifs with hi
    · have he : ε*(D/ε)=D := by field_simp
      rw [he]
      exact hfar i hi
    · simpa only [mul_one] using hnear i hi
  have hfilter : S.filter (· ∈ O)=S ∩ O := by ext i; simp
  have hratio : (∏ i ∈ S, if i ∈ O then D/ε else (1:ℝ))=(D/ε)^(S ∩ O).card := by
    rw [Finset.prod_ite]
    simp [hfilter,div_pow]
  calc
    _ ≤ ∏ i ∈ S, ε*(if i ∈ O then D/ε else 1) :=
      Finset.prod_le_prod (fun _ _ => norm_nonneg _) (fun i _ => hpoint i)
    _ = _ := by rw [Finset.prod_mul_distrib,Finset.prod_const,hratio]





end
end DerivativeChainClusterAnchor


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Finset Polynomial
open DerivativeChainClusterAnchor




theorem solution {n m r : ℕ} (a : Fin n → ℂ) (c : ℂ)
    (O : Finset (Fin n)) (hn : 0 < n) (hm : m ≤ n) (hO : O.card ≤ r)
    (ε D : ℝ) (hε : 0 < ε) (hεD : ε ≤ D)
    (hnear : ∀ i, i ∉ O → ‖c-a i‖ ≤ ε) (hfar : ∀ i, i ∈ O → ‖c-a i‖ ≤ D) :
    ‖(_root_.DerivativeChainClusterAnchor.ordinaryRow a m).eval c‖ ≤ ε^m*(1+D*(m:ℝ)/((n:ℝ)*ε))^r := by
  have hnR : (0:ℝ) < n := by exact_mod_cast hn
  have hD : 0 ≤ D := hε.le.trans hεD
  have ht : 0 ≤ D/ε-1 := by apply sub_nonneg.mpr; exact (one_le_div hε).mpr hεD
  have hbase : 1+(m:ℝ)/(n:ℝ)*(D/ε-1) ≤ 1+D*(m:ℝ)/((n:ℝ)*ε) := by
    have he : (1+D*(m:ℝ)/((n:ℝ)*ε))-(1+(m:ℝ)/(n:ℝ)*(D/ε-1))=(m:ℝ)/(n:ℝ) := by
      field_simp
      ring
    have hnonneg : 0 ≤ (m:ℝ)/(n:ℝ) := by positivity
    linarith
  calc
    _ ≤ (n.choose m:ℝ)⁻¹ * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        ∏ i ∈ S, ‖c-a i‖ := _root_.DerivativeChainClusterAnchor.ordinaryRow_eval_norm_subset_bound a hm c
    _ ≤ (n.choose m:ℝ)⁻¹ * ∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        ε^m*(D/ε)^(S ∩ O).card := by
      apply mul_le_mul_of_nonneg_left _ (by positivity)
      apply Finset.sum_le_sum
      intro S hS
      simpa only [(Finset.mem_powersetCard.mp hS).2] using
        _root_.DerivativeChainClusterAnchor.cluster_subset_norm_product a c O S ε D hε hnear hfar
    _ = ε^m*((∑ S ∈ (Finset.univ : Finset (Fin n)).powersetCard m,
        (1+(D/ε-1))^(S ∩ O).card)/(n.choose m:ℝ)) := by
      simp only [add_sub_cancel,← Finset.mul_sum,div_eq_mul_inv]
      ring
    _ ≤ ε^m*(1+(m:ℝ)/(n:ℝ)*(D/ε-1))^O.card :=
      mul_le_mul_of_nonneg_left (_root_.DerivativeChainClusterAnchor.sampled_exponential_bound O m hn hm (D/ε-1) ht)
        (pow_nonneg hε.le _)
    _ ≤ ε^m*(1+D*(m:ℝ)/((n:ℝ)*ε))^r := by
      apply mul_le_mul_of_nonneg_left _ (pow_nonneg hε.le _)
      exact (pow_le_pow_left₀ (by positivity) hbase _).trans
        (pow_le_pow_right₀ (by
          have hq : 0 ≤ D*(m:ℝ)/((n:ℝ)*ε) := by positivity
          linarith : 1 ≤ 1+D*(m:ℝ)/((n:ℝ)*ε)) hO)
