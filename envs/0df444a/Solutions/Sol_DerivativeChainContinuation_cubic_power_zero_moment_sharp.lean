-- Prove2me | solution 1 for DerivativeChainContinuation.cubic_power_zero_moment_sharp
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:09:49.116055+00:00
-- url     : https://prove2.me/submissions/bf5e317b-fdde-42a8-b53b-cf4665d4a6b7

import Mathlib
import Definitions.Def_DerivativeChainContinuation_SharpCubicConstant
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_cubic_perturbation_disk
import Theorems.Thm_DerivativeChainPrivate_framed_power_chain_collision_limit
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

theorem power_root_inherited_derivative (q : Polynomial ℂ) (h k : ℕ)
    (z : ℂ) (hz : q.eval z = 0) (hk : k < h) :
    (Polynomial.derivative^[k] (q ^ h)).eval z = 0 := by
  obtain ⟨p, hp⟩ := Polynomial.pow_sub_dvd_iterate_derivative_pow q h k
  rw [hp, Polynomial.eval_mul, Polynomial.eval_pow, hz,
    zero_pow (show h - k ≠ 0 by omega), zero_mul]



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

theorem linear_factor_coeff_tendsto (a : ℕ → ℂ) (a₀ : ℂ) (ha : Tendsto a atTop (𝓝 a₀)) :
    ∀ k, Tendsto (fun j => (X-C (a j)).coeff k) atTop (𝓝 ((X-C a₀).coeff k)) := by
  intro k
  by_cases hk : k = 0
  · subst k
    simpa only [coeff_sub,coeff_X_zero,coeff_C_zero,zero_sub] using ha.neg
  · simp only [coeff_sub,coeff_C,if_neg hk,sub_zero]
    exact tendsto_const_nhds





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cubic_moment_perturbation (u v w t : ℂ) :
    let η := (u+v+w)/3
    let a := u-η
    let U := u+t*a
    let V := v-t*a/2
    let W := w-t*a/2
    (U^2+V^2+W^2-U*V-U*W-V*W)/3 =
      (u^2+v^2+w^2-u*v-u*w-v*w)/3+(3/4)*t*(2+t)*a^2 := by
  dsimp only
  ring

theorem cubic_zero_moment_centered_root (u v w : ℂ)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 = 0)
    (hu : u-(u+v+w)/3 = 0) : u = v ∧ v = w := by
  have hη := sub_eq_zero.mp hu
  have hw : w = 2*u-v := by linear_combination (-3 : ℂ)*hη
  rw [hw] at hA
  have hs : (v-u)^2 = 0 := by linear_combination hA
  have hv : v = u := sub_eq_zero.mp ((pow_eq_zero_iff (by norm_num : (2 : ℕ) ≠ 0)).mp hs)
  refine ⟨hv.symm,?_⟩
  rw [hw,hv]
  ring

theorem cubic_zero_moment_perturb_nonzero (u v w : ℂ) (t : ℝ) (ht : 0 < t)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 = 0)
    (ha : u-(u+v+w)/3 ≠ 0) :
    let a := u-(u+v+w)/3
    let U := u+(t : ℂ)*a
    let V := v-(t : ℂ)*a/2
    let W := w-(t : ℂ)*a/2
    (U^2+V^2+W^2-U*V-U*W-V*W)/3 ≠ 0 := by
  have h := cubic_moment_perturbation u v w (t : ℂ)
  dsimp only at h ⊢
  rw [hA,zero_add] at h
  rw [h]
  have htC : (t : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr ht.ne'
  have hsum : 2+(t : ℂ) ≠ 0 := by
    have hp : (2 : ℝ)+t ≠ 0 := ne_of_gt (by linarith)
    exact_mod_cast hp
  exact mul_ne_zero (mul_ne_zero (mul_ne_zero (by norm_num) htC) hsum) (pow_ne_zero 2 ha)



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
namespace DerivativeChainContinuation



theorem sharpCubicConstant_positive : 0 < sharpCubicConstant := by
  unfold sharpCubicConstant
  positivity









end DerivativeChainContinuation



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate
open Polynomial

theorem triple_power_natDegree (u v w : ℂ) (h : ℕ) :
    (((X-C u)*(X-C v)*(X-C w))^h : Polynomial ℂ).natDegree=3*h := by
  rw [natDegree_pow]
  have hq : ((X-C u)*(X-C v)*(X-C w) : Polynomial ℂ).natDegree=3 := by compute_degree <;> norm_num
  rw [hq,Nat.mul_comm]



end DerivativeChainPrivate

open DerivativeChainContinuation in
theorem solution (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hnonzero : ∀ u v w o : ℂ, ∀ R : ℝ, ‖u-o‖ ≤ R → ‖v-o‖ ≤ R → ‖w-o‖ ≤ R →
      (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0 →
      let q := (X-C u)*(X-C v)*(X-C w)
      ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
        (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
        z 0=(u+v+w)/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
        ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
        Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
        chainCost z ≤ sharpCubicConstant*R)
    (u v w o : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3=0) :
    let q := (X-C u)*(X-C v)*(X-C w)
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
      z 0=(u+v+w)/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ sharpCubicConstant*R := by
  classical
  let q : Polynomial ℂ := (X-C u)*(X-C v)*(X-C w)
  let η := (u+v+w)/3
  let d := u-η
  by_cases hd : d=0
  · obtain ⟨hUV,hVW⟩ := cubic_zero_moment_centered_root u v w hA hd
    subst v
    subst w
    let f : Fin (3*h) → ℂ := fun _ => u
    have hpower : q^h=(X-C u)^(3*h) := by
      dsimp only [q]
      rw [show (X-C u)*(X-C u)*(X-C u)=(X-C u)^3 by ring,← pow_mul]
    refine ⟨f,1,-Complex.I,?_,?_,(by intros; rfl),?_,by simp,by simp,by simp,?_,?_,?_⟩
    · intro i
      change (derivative^[3*h-(i.val+1)] (q^h)).eval u=0
      rw [hpower]
      exact power_root_inherited_derivative (X-C u) (3*h) _ u (by simp) (by omega)
    · change u=(u+u+u)/3
      ring
    · simp [q,f]
    · intro i j hij
      exact le_rfl
    · intro i j hij
      exact le_rfl
    · have hc : chainCost f=0 := by simp [f,chainCost]
      rw [hc]
      exact mul_nonneg sharpCubicConstant_positive.le hR
  · let ε : ℕ → ℝ := fun j => (1/2)^j
    have hεpos (j : ℕ) : 0 < ε j := pow_pos (by norm_num) j
    have hεone (j : ℕ) : ε j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hεlim : Tendsto ε atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num)
    have hεC : Tendsto (fun j => (ε j:ℂ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hεlim
    let U (j : ℕ) := u+(ε j:ℂ)*d
    let V (j : ℕ) := v-(ε j:ℂ)*d/2
    let W (j : ℕ) := w-(ε j:ℂ)*d/2
    let r (j : ℕ) := R+ε j*‖d‖
    let Q (j : ℕ) : Polynomial ℂ := (X-C (U j))*(X-C (V j))*(X-C (W j))
    let P (j : ℕ) := Q j^h
    have hmoment (j : ℕ) : (U j^2+V j^2+W j^2-U j*V j-U j*W j-V j*W j)/3 ≠ 0 :=
      cubic_zero_moment_perturb_nonzero u v w (ε j) (hεpos j) hA hd
    have hdisks (j : ℕ) : ‖U j-o‖ ≤ r j ∧ ‖V j-o‖ ≤ r j ∧ ‖W j-o‖ ≤ r j :=
      cubic_perturbation_disk u v w o d R (ε j) (hεpos j).le hu hv hw
    have hsolutions (j : ℕ) := hnonzero (U j) (V j) (W j) o (r j)
      (hdisks j).1 (hdisks j).2.1 (hdisks j).2.2 (hmoment j)
    choose z A B hzroot hzstart hztail hzend hAunit hBunit hab hmonoA hmonoB hcost using hsolutions
    have hcentroid (j : ℕ) : (U j+V j+W j)/3=η := by dsimp [U,V,W,η]; ring
    have hδlim : Tendsto (fun j => (ε j:ℂ)*d) atTop (𝓝 0) := by
      simpa only [zero_mul] using hεC.mul (tendsto_const_nhds (x:=d))
    have hUlim : Tendsto U atTop (𝓝 u) := by
      simpa only [U,add_zero] using (tendsto_const_nhds (x:=u)).add hδlim
    have hVlim : Tendsto V atTop (𝓝 v) := by
      simpa only [V,zero_div,sub_zero] using (tendsto_const_nhds (x:=v)).sub (hδlim.div_const 2)
    have hWlim : Tendsto W atTop (𝓝 w) := by
      simpa only [W,zero_div,sub_zero] using (tendsto_const_nhds (x:=w)).sub (hδlim.div_const 2)
    have hQcoeff : ∀ k, Tendsto (fun j => (Q j).coeff k) atTop (𝓝 (q.coeff k)) :=
      polynomial_coeff_mul_tendsto (fun j => (X-C (U j))*(X-C (V j))) (fun j => X-C (W j))
        ((X-C u)*(X-C v)) (X-C w)
        (polynomial_coeff_mul_tendsto (fun j => X-C (U j)) (fun j => X-C (V j)) (X-C u) (X-C v)
          (linear_factor_coeff_tendsto U u hUlim) (linear_factor_coeff_tendsto V v hVlim))
        (linear_factor_coeff_tendsto W w hWlim)
    have hPcoeff : ∀ k, Tendsto (fun j => (P j).coeff k) atTop (𝓝 ((q^h).coeff k)) :=
      polynomial_coeff_pow_tendsto Q q hQcoeff h
    have hPdeg (j : ℕ) : (P j).natDegree=3*h := triple_power_natDegree (U j) (V j) (W j) h
    have hqdeg : (q^h).natDegree=3*h := triple_power_natDegree u v w h
    let M := R+‖d‖+‖o‖
    have hM : 0 ≤ M := by dsimp [M]; positivity
    have hrmax (j : ℕ) : r j ≤ R+‖d‖ := by
      have ht := mul_le_mul_of_nonneg_right (hεone j) (norm_nonneg d)
      dsimp only [r]
      linarith only [ht]
    have hsourceBound (j : ℕ) (x : ℂ) (hx : (P j).eval x=0) : ‖x‖ ≤ M := by
      have hpow : ((Q j).eval x)^h=0 := by simpa only [P,eval_pow] using hx
      have hqroot : (Q j).eval x=0 := (pow_eq_zero_iff (Nat.ne_of_gt hh)).mp hpow
      have hcases : x=U j ∨ x=V j ∨ x=W j := by
        simpa only [Q,eval_mul,eval_sub,eval_X,eval_C,mul_eq_zero,sub_eq_zero,or_assoc] using hqroot
      have hDisk : ‖x-o‖ ≤ r j := by
        rcases hcases with ht|ht|ht
        · rw [ht]; exact (hdisks j).1
        · rw [ht]; exact (hdisks j).2.1
        · rw [ht]; exact (hdisks j).2.2
      have hnorm : ‖x‖ ≤ ‖x-o‖+‖o‖ := by simpa only [sub_add_cancel] using norm_add_le (x-o) o
      change ‖x‖ ≤ R+‖d‖+‖o‖
      linarith only [hnorm,hDisk,hrmax j]
    have hzbound (j : ℕ) (i : Fin (3*h)) : ‖z j i‖ ≤ M :=
      iterate_derivative_norm_bound (P j) (3*h-(i.val+1)) (by rw [hPdeg]; omega)
        M (hsourceBound j) (z j i) (hzroot j i)
    let costs (j : ℕ) := sharpCubicConstant*r j
    have hrLim : Tendsto r atTop (𝓝 R) := by
      simpa only [r,zero_mul,add_zero] using
        (tendsto_const_nhds (x:=R)).add (hεlim.mul (tendsto_const_nhds (x:=‖d‖)))
    have hCLim : Tendsto costs atTop (𝓝 (sharpCubicConstant*R)) :=
      (tendsto_const_nhds (x:=sharpCubicConstant)).mul hrLim
    obtain ⟨f,A',B',hfroot,hfstart,hftail,hA',hB',horth,hmono₀,hmono₁,hfcost⟩ :=
      framed_power_chain_collision_limit (3*h) (2*h) last P (q^h)
        (fun j => (hPdeg j).le) hqdeg.le hPcoeff z A B M hM hzbound hzroot η
        (fun j => (hzstart j).trans (hcentroid j)) hztail hAunit hBunit hab hmonoA hmonoB costs _ hCLim hcost
    have hqend : q.eval (f last)=0 := by
      have hr := hfroot last
      have hk : 3*h-(last.val+1)=0 := by omega
      rw [hk,Function.iterate_zero_apply,eval_pow] at hr
      exact (pow_eq_zero_iff (Nat.ne_of_gt hh)).mp hr
    exact ⟨f,A',B',hfroot,hfstart,hftail,hqend,hA',hB',horth,hmono₀,hmono₁,hfcost⟩
