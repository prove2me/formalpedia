-- Prove2me | solution 1 for DerivativeChainClusterAnchor.baseline_complete_chain_radius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T05:49:01.936427+00:00
-- url     : https://prove2.me/submissions/9b76d344-3101-4d97-a6b0-2414af5f8bf2

import Mathlib
import Definitions.Def_DerivativeChainAnalytic_ClusterSubsetProduct
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainClusterAnchor_ordinaryRow_eval_zero_of_exact_cluster
import Theorems.Thm_DerivativeChainPrivate_exists_chain_cost_le_sqrt
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


open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







theorem chainCost_scale {n : ℕ} (z : Fin n → ℂ) (c : ℂ) :
    chainCost (fun i => c * z i) = ‖c‖ * chainCost z := by
  simp only [chainCost, ← mul_sub, norm_mul, Finset.mul_sum]

end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate











theorem chainCost_translate {n : ℕ} (z : Fin n → ℂ) (u : ℂ) :
    chainCost (fun i => z i + u) = chainCost z := by
  simp only [chainCost, add_sub_add_right_eq_sub]

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate







end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem iterate_derivative_comp_affine (p : Polynomial ℂ) (a c : ℂ) (k : ℕ) :
    derivative^[k] (p.comp (C a+C c*X)) =
      C (c^k)*(derivative^[k] p).comp (C a+C c*X) := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [Function.iterate_succ_apply',ih,derivative_C_mul,derivative_comp]
    simp only [derivative_add,derivative_C,derivative_mul,zero_mul,derivative_X,
      mul_one,zero_add,Function.iterate_succ_apply']
    rw [pow_succ,C_mul]
    ring

theorem affine_derivative_root (P Q : Polynomial ℂ) (a c d : ℂ) (hc : c ≠ 0)
    (hcomp : P.comp (C a+C c*X) = C d*Q) (k : ℕ) (z : ℂ)
    (hz : (derivative^[k] Q).eval z = 0) :
    (derivative^[k] P).eval (a+c*z) = 0 := by
  have h := congrArg (fun p : Polynomial ℂ => (derivative^[k] p).eval z) hcomp
  rw [iterate_derivative_comp_affine,iterate_derivative_C_mul] at h
  simp only [eval_mul,eval_C,eval_comp,eval_add,eval_X,hz,mul_zero] at h
  exact (mul_eq_zero.mp h).resolve_left (pow_ne_zero k hc)

theorem chainCost_affine {n : ℕ} (z : Fin n → ℂ) (a c : ℂ) :
    chainCost (fun i => a+c*z i) = ‖c‖*chainCost z := by
  have hfun : (fun i => a+c*z i) = (fun i => c*z i+a) := by funext i; ring
  rw [hfun,chainCost_translate,chainCost_scale]



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial







end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate



end DerivativeChainPrivate



set_option autoImplicit false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial











end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate









end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



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
open Polynomial DerivativeChainPrivate
open DerivativeChainClusterAnchor




theorem solution {n : ℕ} (hn : 0 < n) (a : Fin n → ℂ)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hall : ∀ i, ‖a i-o‖ ≤ R) :
    ∃ z : Fin n → ℂ, _root_.DerivativeChainPrivate.IsChain a z ∧
      _root_.DerivativeChainPrivate.chainCost z ≤ Real.sqrt ((n-1:ℕ):ℝ)*R := by
  by_cases hzero : R=0
  · subst R
    obtain ⟨z,hz,hcost⟩ := _root_.DerivativeChainClusterAnchor.zero_radius_complete_chain hn a o hall
    exact ⟨z,hz,by simp [hcost]⟩
  · have hRpos : 0 < R := lt_of_le_of_ne hR (Ne.symm hzero)
    have hRC : (R:ℂ) ≠ 0 := by exact_mod_cast hzero
    let b : Fin n → ℂ := fun i => (a i-o)/(R:ℂ)
    have hb (i : Fin n) : ‖b i‖ ≤ 1 := by
      dsimp [b]
      rw [norm_div,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hRpos]
      exact (div_le_one hRpos).mpr (hall i)
    obtain ⟨w,hw,hcost⟩ := _root_.DerivativeChainPrivate.exists_chain_cost_le_sqrt hn b hb
    have hfactor (i : Fin n) : C o+C (R:ℂ)*X-C (a i)=C (R:ℂ)*(X-C (b i)) := by
      have hi : (R:ℂ)*b i=a i-o := by dsimp [b]; field_simp
      rw [mul_sub,← C_mul,hi,C_sub]
      ring
    have hcomp : (_root_.DerivativeChainPrivate.fromRoots a).comp (C o+C (R:ℂ)*X)=C ((R:ℂ)^n)*_root_.DerivativeChainPrivate.fromRoots b := by
      unfold _root_.DerivativeChainPrivate.fromRoots
      rw [Polynomial.prod_comp]
      simp only [sub_comp,X_comp,C_comp]
      calc
        _ = ∏ i : Fin n, C (R:ℂ)*(X-C (b i)) := Finset.prod_congr rfl (fun i _ => hfactor i)
        _ = (∏ _i : Fin n, C (R:ℂ))*(∏ i : Fin n, (X-C (b i))) := Finset.prod_mul_distrib
        _ = _ := by simp only [Finset.prod_const,Finset.card_univ,Fintype.card_fin,← map_pow]
    refine ⟨(fun i => o+(R:ℂ)*w i),?_,?_⟩
    · intro i
      exact _root_.DerivativeChainPrivate.affine_derivative_root (_root_.DerivativeChainPrivate.fromRoots a) (_root_.DerivativeChainPrivate.fromRoots b) o (R:ℂ) ((R:ℂ)^n)
        hRC hcomp (n-(i.val+1)) (w i) (hw i)
    · rw [_root_.DerivativeChainPrivate.chainCost_affine,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hRpos]
      exact (mul_le_mul_of_nonneg_left hcost hR).trans_eq (mul_comm _ _)
