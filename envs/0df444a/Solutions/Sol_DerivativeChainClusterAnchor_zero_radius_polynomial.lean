-- Prove2me | solution 1 for DerivativeChainClusterAnchor.zero_radius_polynomial
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-28T04:02:35.219004+00:00
-- url     : https://prove2.me/submissions/f37440ca-cee7-4986-8e86-01e04a7cc358

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_actual_polynomial_slots
import Theorems.Thm_DerivativeChainClusterAnchor_ordinaryRow_eval_zero_of_exact_cluster
set_option autoImplicit false
namespace DerivativeChain
end DerivativeChain
namespace DerivativeChainClusterAnchor
end DerivativeChainClusterAnchor
namespace DerivativeChainContinuation
end DerivativeChainContinuation
namespace DerivativeChainPrefixLaws
end DerivativeChainPrefixLaws
namespace DerivativeChainPrivate
end DerivativeChainPrivate


set_option autoImplicit false
set_option maxHeartbeats 1000000
open scoped BigOperators
open Polynomial
namespace DerivativeChainClusterAnchor
noncomputable section















theorem ordinaryRow_eval_zero_iff {n m : ℕ} (a : Fin n → ℂ) (c : ℂ) :
    (ordinaryRow a m).eval c=0 ↔ (derivative^[n-m] (sourcePolynomial a)).eval c=0 := by
  have hc : ((m.factorial:ℂ)/(n.factorial:ℂ)) ≠ 0 :=
    div_ne_zero (by exact_mod_cast Nat.factorial_ne_zero m) (by exact_mod_cast Nat.factorial_ne_zero n)
  simp only [ordinaryRow,eval_mul,eval_C,mul_eq_zero,hc,false_or]



end
end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainPrivate
namespace DerivativeChainClusterAnchor
noncomputable section

theorem zero_radius_complete_chain {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ) (o : ℂ)
    (hall : ∀ i, ‖a i-o‖ ≤ 0) :
    ∃ z : Fin n → ℂ, DerivativeChainPrivate.IsChain a z ∧ chainCost z=0 := by
  have ha (i : Fin n) : a i=o := sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm (hall i) (norm_nonneg _)))
  refine ⟨(fun _ => o),?_,?_⟩
  · intro i
    have hh := ordinaryRow_eval_zero_of_exact_cluster a o ∅ (by omega : i.val+1 ≤ n)
      (by simp : (∅ : Finset (Fin n)).card ≤ 0) (by omega : 0 < i.val+1) (fun j _ => ha j)
    have hr := (ordinaryRow_eval_zero_iff a o).mp hh
    simpa only [row,fromRoots,sourcePolynomial] using hr
  · simp [chainCost]



end
end DerivativeChainClusterAnchor



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1500000
open scoped BigOperators
open Polynomial DerivativeChainContinuation DerivativeChainPrivate
open DerivativeChainClusterAnchor












theorem solution (p : ℂ[X]) (hp : p.Monic) (n : ℕ)
    (hdegree : p.natDegree=n) (hn : 0 < n) (o : ℂ)
    (hsource : ∀ z ∈ p.roots, ‖z-o‖ ≤ 0) :
    p=(X-C o)^n ∧ ∃ z : Fin n → ℂ,
      (∀ i, (derivative^[n-(i.val+1)] p).eval (z i)=0) ∧ _root_.DerivativeChainPrivate.chainCost z=0 := by
  classical
  obtain ⟨a,hpa,hmem,_⟩ := _root_.DerivativeChainClusterAnchor.actual_polynomial_slots p hp n hdegree (fun _ => True)
  have ha (i : Fin n) : a i=o := sub_eq_zero.mp
    (norm_eq_zero.mp (le_antisymm (hsource (a i) (hmem i)) (norm_nonneg _)))
  have hpure : p=(X-C o)^n := by rw [hpa,_root_.DerivativeChainPrivate.fromRoots]; simp only [ha,Finset.prod_const,Finset.card_univ,Fintype.card_fin]
  obtain ⟨z,hz,hcost⟩ := _root_.DerivativeChainClusterAnchor.zero_radius_complete_chain hn a o (fun i => hsource (a i) (hmem i))
  refine ⟨hpure,z,?_,hcost⟩
  intro i
  rw [hpa]
  exact hz i
