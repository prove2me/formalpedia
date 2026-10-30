-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_power_chain_boundary
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T02:50:48.665979+00:00
-- url     : https://prove2.me/submissions/7d674d80-948c-43d9-937a-320f410bd0ea

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainContinuation_coordinate_chain_collision_limit_with_fixed_start
import Theorems.Thm_DerivativeChainPrivate_finite_coordinate_chain_cost
import Theorems.Thm_DerivativeChainPrivate_iterate_derivative_norm_bound
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

theorem polynomial_coeff_mul_tendsto (p q : ℕ → Polynomial ℂ) (P Q : Polynomial ℂ)
    (hp : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (P.coeff k)))
    (hq : ∀ k, Tendsto (fun j => (q j).coeff k) atTop (𝓝 (Q.coeff k))) :
    ∀ k, Tendsto (fun j => (p j*q j).coeff k) atTop (𝓝 ((P*Q).coeff k)) := by
  intro k
  simp only [coeff_mul]
  exact tendsto_finsetSum _ (fun i _ => (hp i.1).mul (hq i.2))

theorem polynomial_coeff_pow_tendsto (p : ℕ → Polynomial ℂ) (P : Polynomial ℂ)
    (hp : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (P.coeff k))) (m : ℕ) :
    ∀ k, Tendsto (fun j => (p j^m).coeff k) atTop (𝓝 ((P^m).coeff k)) := by
  induction m with
  | zero => intro k; simpa only [pow_zero] using (tendsto_const_nhds :
      Tendsto (fun _ : ℕ => (1 : Polynomial ℂ).coeff k) atTop (𝓝 ((1 : Polynomial ℂ).coeff k)))
  | succ m ih =>
    simpa only [pow_succ] using polynomial_coeff_mul_tendsto (fun j => p j^m) p (P^m) P ih hp







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
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial

theorem depressed_cubic_root_norm_bound (a b B : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (hB : 0 ≤ B)
    (β z : ℂ) (hβ : ‖β‖ ≤ B) (hroot : z^3-(a:ℂ)*z-(b:ℂ)*β=0) :
    ‖z‖ ≤ a+b*B+2 := by
  have he : z^3=(a:ℂ)*z+(b:ℂ)*β := by linear_combination hroot
  have hn : ‖z‖^3 ≤ a*‖z‖+b*B := by
    calc
      _ = ‖(a:ℂ)*z+(b:ℂ)*β‖ := by rw [← he,norm_pow]
      _ ≤ ‖(a:ℂ)*z‖+‖(b:ℂ)*β‖ := norm_add_le _ _
      _ = a*‖z‖+b*‖β‖ := by simp [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ha,abs_of_nonneg hb]
      _ ≤ _ := by gcongr
  by_contra h
  have hr : a+b*B+2 < ‖z‖ := lt_of_not_ge h
  have hc : 0 ≤ b*B := mul_nonneg hb hB
  have hr1 : 1 ≤ ‖z‖ := by linarith
  have hr2 : ‖z‖ ≤ ‖z‖^2 := by nlinarith [norm_nonneg z]
  have hr3 : ‖z‖^2 ≤ ‖z‖^3 := by
    have hh := mul_le_mul_of_nonneg_left hr2 (norm_nonneg z)
    nlinarith only [hh]
  have hm := mul_pos (show 0 < ‖z‖-a-b*B-2 by linarith) (show 0 < ‖z‖ by linarith)
  have hcprod := mul_nonneg hc (show 0 ≤ ‖z‖-1 by linarith)
  nlinarith only [hn,hr3,hm,hcprod,hr1]



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hstrict : ∀ β : ℂ, 0 ≤ β.re → 0 < β.im → ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im))
    (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval (z last)=0 ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2*‖z last‖ := by
  let ε : ℕ → ℝ := fun j => (1/2)^j
  let γ : ℕ → ℂ := fun j => β+(ε j:ℂ)*Complex.I
  let q : ℂ → Polynomial ℂ := fun t => X^3-C (a:ℂ)*X-C ((b:ℂ)*t)
  let P : ℕ → Polynomial ℂ := fun j => (q (γ j))^h
  have hεpos (j : ℕ) : 0 < ε j := pow_pos (by norm_num) j
  have hεone (j : ℕ) : ε j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
  have hεlim : Tendsto ε atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
  have hεC : Tendsto (fun j => (ε j:ℂ)) atTop (𝓝 0) := by
    simpa only [Function.comp_def,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hεlim
  have hγlim : Tendsto γ atTop (𝓝 β) := by
    simpa only [γ,zero_mul,add_zero] using (tendsto_const_nhds (x:=β)).add (hεC.mul_const Complex.I)
  have hγR (j : ℕ) : 0 ≤ (γ j).re := by simpa [γ] using hR
  have hγI (j : ℕ) : 0 < (γ j).im := by simp only [γ,Complex.add_im,Complex.mul_im,Complex.ofReal_re,
    Complex.ofReal_im,Complex.I_im,Complex.I_re,mul_one,mul_zero,add_zero]; linarith [hεpos j]
  have hsolutions (j : ℕ) := hstrict (γ j) (hγR j) (hγI j)
  choose z hzroot hzstart hztail hzmonoR hzmonoI using hsolutions
  have hγnorm (j : ℕ) : ‖γ j‖ ≤ ‖β‖+1 := by
    have hn := norm_add_le β ((ε j:ℂ)*Complex.I)
    have he : ‖(ε j:ℂ)*Complex.I‖=ε j := by simp [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_pos (hεpos j)]
    rw [he] at hn
    exact hn.trans (by linarith [hεone j])
  have hqcoeff : ∀ k, Tendsto (fun j => (q (γ j)).coeff k) atTop (𝓝 ((q β).coeff k)) := by
    intro k
    by_cases hk : k=0
    · subst k
      simpa [q] using ((tendsto_const_nhds (x:=(b:ℂ))).mul hγlim).neg
    · simp only [q,coeff_sub,coeff_C,if_neg hk,sub_zero]
      exact tendsto_const_nhds
  have hPcoeff := polynomial_coeff_pow_tendsto (fun j => q (γ j)) (q β) hqcoeff h
  have hdegree (t : ℂ) : ((q t)^h).natDegree=3*h := by
    rw [natDegree_pow]
    have hqd : (q t).natDegree=3 := by dsimp [q]; compute_degree <;> norm_num
    rw [hqd,Nat.mul_comm]
  let M := a+b*(‖β‖+1)+2
  have hM : 0 ≤ M := by dsimp [M]; positivity
  have hsource (j : ℕ) (x : ℂ) (hx : (P j).eval x=0) : ‖x‖ ≤ M := by
    have hpow : ((q (γ j)).eval x)^h=0 := by simpa only [P,eval_pow] using hx
    have hqr := (pow_eq_zero_iff (Nat.ne_of_gt hh)).mp hpow
    have hqr' : x^3-(a:ℂ)*x-(b:ℂ)*(γ j)=0 := by
      simpa only [q,eval_sub,eval_mul,eval_pow,eval_X,eval_C] using hqr
    exact depressed_cubic_root_norm_bound a b (‖β‖+1) ha hb (by positivity) (γ j) x (hγnorm j) hqr'
  have hbound (j : ℕ) (i : Fin (3*h)) : ‖z j i‖ ≤ M := by
    apply iterate_derivative_norm_bound (P j) (3*h-(i.val+1)) _ M (hsource j) (z j i) (hzroot j i)
    change 3*h-(i.val+1) < ((q (γ j))^h).natDegree
    rw [hdegree]
    omega
  obtain ⟨w,hwroot,hwstart,hwtail,hwR,hwI⟩ := DerivativeChainContinuation.coordinate_chain_collision_limit_with_fixed_start (3*h) (2*h) last P ((q β)^h)
    (fun j => (hdegree (γ j)).le) (hdegree β).le hPcoeff z M hM hbound hzroot 0 hzstart hztail hzmonoR hzmonoI
  have hend : (q β).eval (w last)=0 := by
    have hr := hwroot last
    have hk : 3*h-(last.val+1)=0 := by omega
    rw [hk,Function.iterate_zero_apply,eval_pow] at hr
    exact (pow_eq_zero_iff (Nat.ne_of_gt hh)).mp hr
  refine ⟨w,hwroot,hwstart,hwtail,hend,hwR,hwI,?_⟩
  have hc := finite_coordinate_chain_cost (3*h) w last hlast hwR hwI
  simpa only [hwstart,sub_zero] using hc
