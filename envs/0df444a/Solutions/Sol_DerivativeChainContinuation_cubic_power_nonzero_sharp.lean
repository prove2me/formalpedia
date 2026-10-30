-- Prove2me | solution 1 for DerivativeChainContinuation.cubic_power_nonzero_sharp
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:02:02.174557+00:00
-- url     : https://prove2.me/submissions/dd514aa6-6df5-414c-9684-65cb5661522a

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_normalized_power_sharp_disk
import Theorems.Thm_DerivativeChainPrivate_affine_orthonormal_coordinates
import Theorems.Thm_DerivativeChainPrivate_cubic_triple_normalization_parameters
open DerivativeChainPrivate Polynomial MeasureTheory Filter Set Topology Metric Function ComplexConjugate
open scoped BigOperators ComplexOrder Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


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



open DerivativeChainContinuation in
theorem solution (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hstrict : ∀ β : ℂ, 0 ≤ β.re → 0 < β.im → ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im))
    (u v w o : ℂ) (R : ℝ) (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0) :
    let q := (X-C u)*(X-C v)*(X-C w)
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
      z 0=(u+v+w)/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ sharpCubicConstant*R := by
  let q : Polynomial ℂ := (X-C u)*(X-C v)*(X-C w)
  let η := (u+v+w)/3
  obtain ⟨c,β,hc,hβ,hcomp⟩ := cubic_triple_normalization_parameters u v w a b ha hb hA
  have hR : 0 ≤ R := (norm_nonneg _).trans hu
  have hcn : ‖c‖ ≠ 0 := norm_ne_zero_iff.mpr hc
  have hnormal (z : ℂ) (hz : (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval z=0) :
      ‖z-(o-η)/c‖ ≤ R/‖c‖ := by
    have hroot : q.eval (η+c*z)=0 :=
      affine_derivative_root q (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)) η c (c^3) hc hcomp 0 z hz
    have hcases : η+c*z=u ∨ η+c*z=v ∨ η+c*z=w := by
      simpa only [q,eval_mul,eval_sub,eval_X,eval_C,mul_eq_zero,sub_eq_zero,or_assoc] using hroot
    have hdisk : ‖η+c*z-o‖ ≤ R := by
      rcases hcases with ht|ht|ht
      · rwa [ht]
      · rwa [ht]
      · rwa [ht]
    have he : z-(o-η)/c=(η+c*z-o)/c := by field_simp; ring
    rw [he,norm_div]
    exact div_le_div_of_nonneg_right hdisk (norm_nonneg c)
  obtain ⟨g,A,B,hroots,hstart,htail,hend,hAunit,hBunit,horth,hmonoA,hmonoB,hcost⟩ :=
    normalized_power_sharp_disk h hh a b ha.le hb.le last hlast hstrict β hβ
      ((o-η)/c) (R/‖c‖) (div_nonneg hR (norm_nonneg c)) hnormal
  let f : Fin (3*h) → ℂ := fun i => η+c*g i
  have hpower : (q^h).comp (C η+C c*X) =
      C (c^(3*h))*(X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h := by
    rw [pow_comp,hcomp,mul_pow,← C_pow,← pow_mul]
  have hfroot (i : Fin (3*h)) : (derivative^[3*h-(i.val+1)] (q^h)).eval (f i)=0 :=
    affine_derivative_root (q^h) ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h) η c (c^(3*h)) hc hpower _ (g i) (hroots i)
  have hqend : q.eval (f last)=0 :=
    affine_derivative_root q (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)) η c (c^3) hc hcomp 0 (g last) hend
  have hfcost : chainCost f ≤ sharpCubicConstant*R := by
    rw [chainCost_affine]
    have hm := mul_le_mul_of_nonneg_left hcost (norm_nonneg c)
    calc
      _ ≤ ‖c‖*(sharpCubicConstant*(R/‖c‖)) := hm
      _ = sharpCubicConstant*R := by field_simp
  obtain ⟨A',B',hA',hB',horth',hmA,hmB⟩ :=
    affine_orthonormal_coordinates g A B η c hc hAunit hBunit horth hmonoA hmonoB
  refine ⟨f,A',B',hfroot,?_,?_,hqend,hA',hB',horth',hmA,hmB,hfcost⟩
  · simp only [f,hstart,mul_zero,add_zero,η]
  · intro i hi; exact congrArg (fun t => η+c*t) (htail i hi)
