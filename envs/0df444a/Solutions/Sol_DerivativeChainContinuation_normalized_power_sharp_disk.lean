-- Prove2me | solution 1 for DerivativeChainContinuation.normalized_power_sharp_disk
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:53:53.252709+00:00
-- url     : https://prove2.me/submissions/69fd9653-0f54-45bb-801b-3318bd4676b3

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_finite_coordinate_chain_cost_l1
import Theorems.Thm_DerivativeChainContinuation_sharp_normalized_cubic_endpoint
import Theorems.Thm_DerivativeChainPrivate_normalized_power_chain_boundary
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









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate













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









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem conjugate_derivative_eval (p : Polynomial ℂ) (k : ℕ) (z : ℂ) :
    (derivative^[k] (p.map (starRingEnd ℂ))).eval (starRingEnd ℂ z) =
      starRingEnd ℂ ((derivative^[k] p).eval z) := by
  have hmap : derivative^[k] (p.map (starRingEnd ℂ)) = (derivative^[k] p).map (starRingEnd ℂ) := by
    induction k with
    | zero => rfl
    | succ k ih => rw [Function.iterate_succ_apply',ih,derivative_map,Function.iterate_succ_apply']
  rw [hmap,eval_map_apply]

theorem chainCost_conjugate {n : ℕ} (z : Fin n → ℂ) :
    chainCost (fun i => starRingEnd ℂ (z i)) = chainCost z := by
  simp only [chainCost,←map_sub,Complex.norm_conj]



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
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hstrict : ∀ β : ℂ, 0 ≤ β.re → 0 < β.im → ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im))
    (β : ℂ) (hβR : 0 ≤ β.re) (o : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hbound : ∀ z : ℂ, (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval z=0 → ‖z-o‖ ≤ R) :
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ sharpCubicConstant*R := by
  have hu := normalized_power_chain_boundary h hh a b ha hb last hlast hstrict
  have hcost (γ : ℂ) (hγR : 0 ≤ γ.re) (hγI : 0 ≤ γ.im) (t : Fin (3*h) → ℂ)
      (ht0 : t 0=0) (htend : (X^3-C (a:ℂ)*X-C ((b:ℂ)*γ)).eval (t last)=0)
      (htR : Monotone (fun i => (t i).re)) (htI : Monotone (fun i => (t i).im))
      (o' : ℂ) (hdisk : ∀ z : ℂ, (X^3-C (a:ℂ)*X-C ((b:ℂ)*γ)).eval z=0 → ‖z-o'‖ ≤ R) :
      chainCost t ≤ sharpCubicConstant*R := by
    have hx := htR (Fin.zero_le last)
    have hy := htI (Fin.zero_le last)
    simp only [ht0,Complex.zero_re,Complex.zero_im] at hx hy
    have hm := sharp_normalized_cubic_endpoint a ha ((b:ℂ)*γ) (t last) o'
      (by simpa [Complex.mul_re] using mul_nonneg hb hγR)
      (by simpa [Complex.mul_im] using mul_nonneg hb hγI)
      (by simpa only [eval_sub,eval_pow,eval_X,eval_mul,eval_C] using htend)
      hx hy R hR (fun z hz => hdisk z (by simpa only [eval_sub,eval_pow,eval_X,eval_mul,eval_C] using hz))
    have hl := finite_coordinate_chain_cost_l1 (3*h) t last hlast htR htI
    simp only [ht0,Complex.zero_re,Complex.zero_im,sub_zero] at hl
    exact hl.trans hm
  by_cases hI : 0 ≤ β.im
  · obtain ⟨z,hroot,hstart,htail,hend,hre,him,_⟩ := hu β hβR hI
    refine ⟨z,1,-Complex.I,hroot,hstart,htail,hend,by simp,by simp,by simp,?_,?_,?_⟩
    · simpa only [one_mul] using hre
    · simpa [Complex.mul_re] using him
    · exact hcost β hβR hI z hstart hend hre him o hbound
  · let γ := starRingEnd ℂ β
    have hγR : 0 ≤ γ.re := by simpa only [γ,Complex.conj_re] using hβR
    have hγI : 0 ≤ γ.im := by dsimp only [γ]; rw [Complex.conj_im]; linarith
    obtain ⟨z,hroot,hstart,htail,hend,hre,him,_⟩ := hu γ hγR hγI
    let f : Fin (3*h) → ℂ := fun i => starRingEnd ℂ (z i)
    have hmap : (((X^3-C (a:ℂ)*X-C ((b:ℂ)*γ))^h : Polynomial ℂ)).map (starRingEnd ℂ) =
        (X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h := by simp [γ]
    have hmapq : ((X^3-C (a:ℂ)*X-C ((b:ℂ)*γ)):Polynomial ℂ).map (starRingEnd ℂ) =
        X^3-C (a:ℂ)*X-C ((b:ℂ)*β) := by simp [γ]
    have hroots (i : Fin (3*h)) : (derivative^[3*h-(i.val+1)]
        ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (f i)=0 := by
      rw [← hmap,conjugate_derivative_eval,hroot,map_zero]
    have hdisk (w : ℂ) (hw : (X^3-C (a:ℂ)*X-C ((b:ℂ)*γ)).eval w=0) :
        ‖w-starRingEnd ℂ o‖ ≤ R := by
      have hr : (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval (starRingEnd ℂ w)=0 := by
        rw [← hmapq,eval_map]
        simpa using congrArg (starRingEnd ℂ) hw
      have ht := hbound _ hr
      have he : ‖w-starRingEnd ℂ o‖=‖starRingEnd ℂ w-o‖ := by
        rw [← Complex.norm_conj (w-starRingEnd ℂ o)]
        simp
      rwa [he]
    have hc := hcost γ hγR hγI z hstart hend hre him (starRingEnd ℂ o) hdisk
    refine ⟨f,1,Complex.I,hroots,?_,?_,?_,by simp,by simp,by simp,?_,?_,?_⟩
    · simpa only [f,hstart,map_zero]
    · intro i hi; exact congrArg (starRingEnd ℂ) (htail i hi)
    · rw [← hmapq,eval_map]; simpa [f] using congrArg (starRingEnd ℂ) hend
    · simpa only [f,one_mul,Complex.conj_re] using hre
    · simpa [f,Complex.mul_re] using him
    · simpa only [f,chainCost_conjugate] using hc
