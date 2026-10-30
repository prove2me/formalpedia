-- Prove2me | solution 1 for DerivativeChainContinuation.collinear_transport_chain_family
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T17:46:20.426278+00:00
-- url     : https://prove2.me/submissions/278a6792-0741-4cf5-825b-125ff3217a18

import Mathlib
import Definitions.Def_DerivativeChainContinuation_CollinearTransport
import Definitions.Def_DerivativeChainContinuation_RealHistories
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainContinuation_RealTransportBound
import Definitions.Def_DerivativeChainContinuation_RealTransportGeneral
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_real_transport_chain_family
open DerivativeChainPrivate
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Polynomial
open scoped BigOperators


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
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainContinuation
open Polynomial DerivativeChainPrivate
open scoped BigOperators



theorem complexCentroid_affine {n : ℕ} (a : Fin (n+1) → ℝ) (o c : ℂ) :
    complexCentroid (fun i => o+c*(a i : ℂ))=o+c*(realCentroid a : ℂ) := by
  have hn : (n+1 : ℂ)≠0 := by exact_mod_cast (show n+1≠0 by omega)
  simp [complexCentroid,realCentroid,Finset.sum_add_distrib,←Finset.mul_sum]
  field_simp

theorem realChainCost_complex {n : ℕ} (z : Fin (n+1) → ℝ) :
    chainCost (fun i => (z i : ℂ))=realChainCost z := by
  simp only [chainCost,realChainCost,Nat.add_sub_cancel]
  change (∑ i : Fin n, ‖((z i.succ : ℂ)-(z i.castSucc : ℂ))‖)=_
  simp only [←Complex.ofReal_sub,Complex.norm_real,Real.norm_eq_abs]

theorem affine_source_comp {n : ℕ} (a : Fin (n+1) → ℝ) (o c : ℂ) :
    (fromRoots (fun i => o+c*(a i : ℂ))).comp (C o+C c*X) =
      C (c^(n+1))*(realRootProduct a).map Complex.ofRealHom := by
  have hf (i : Fin (n+1)) : (X-C (o+c*(a i : ℂ))).comp (C o+C c*X) =
      C c*(X-C (a i : ℂ)) := by
    rw [sub_comp,X_comp,C_comp]
    simp only [map_add,map_mul]
    ring
  simp only [fromRoots,Polynomial.prod_comp,hf,Finset.prod_mul_distrib]
  simp [realRootProduct,Polynomial.map_prod,map_sub]










end DerivativeChainContinuation

open DerivativeChainContinuation in
theorem solution (n : ℕ) (hn : 0<n)
    (a : Fin (n+1) → ℝ) (o c : ℂ) (hc : c≠0) :
    ∃ z : Fin (n+1) → Fin (n+1) → ℂ,
      (∀ j,IsChain (fun i => o+c*(a i : ℂ)) (z j)) ∧
      (∀ j,z j (Fin.last n)=o+c*(a j : ℂ)) ∧
      (∑ j,(chainCost (z j))^2) ≤ (28/3 : ℝ)*
        (∑ i,‖o+c*(a i : ℂ)-complexCentroid (fun j => o+c*(a j : ℂ))‖^2) := by
  obtain ⟨z,hz,he,hcost⟩ := real_transport_chain_family n hn a
  let zz : Fin (n+1) → Fin (n+1) → ℂ := fun j i => o+c*(z j i : ℂ)
  have hcomp := affine_source_comp a o c
  have hnorm (i : Fin (n+1)) :
      ‖o+c*(a i : ℂ)-complexCentroid (fun j => o+c*(a j : ℂ))‖^2 =
        ‖c‖^2*(a i-realCentroid a)^2 := by
    rw [complexCentroid_affine]
    have hf : o+c*(a i : ℂ)-(o+c*(realCentroid a : ℂ)) =
        c*((a i-realCentroid a : ℝ) : ℂ) := by rw [Complex.ofReal_sub]; ring
    rw [hf,norm_mul,mul_pow,Complex.norm_real,Real.norm_eq_abs,sq_abs]
  have hzcost (j : Fin (n+1)) : chainCost (zz j)=‖c‖*realChainCost (z j) := by
    rw [show zz j=(fun i => o+c*(z j i : ℂ)) from rfl,chainCost_affine,realChainCost_complex]
  refine ⟨zz,?_,?_,?_⟩
  · intro j i
    change (derivative^[n+1-(i.val+1)] (fromRoots (fun k => o+c*(a k : ℂ)))).eval (zz j i)=0
    rw [Nat.add_sub_add_right]
    apply affine_derivative_root _ _ o c (c^(n+1)) hc hcomp
    have h := congrArg Complex.ofRealHom (hz j i)
    rw [iterate_derivative_map,eval_map]
    change (((derivative^[n-i.val]) (realRootProduct a)).eval₂ Complex.ofRealHom
      (Complex.ofRealHom (z j i)))=0
    rw [eval₂_at_apply]
    simpa only [map_zero] using h
  · intro j
    simp only [zz,he]
  · simp_rw [hzcost,mul_pow,hnorm]
    rw [←Finset.mul_sum,←Finset.mul_sum]
    have h := mul_le_mul_of_nonneg_left hcost (sq_nonneg ‖c‖)
    nlinarith [h]
