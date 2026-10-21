-- Prove2me | solution 1 for DerivativeChainPrivate.cubicFifthChainRadius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T23:21:15.849068+00:00
-- url     : https://prove2.me/submissions/5cb20721-ceb4-4cb2-8b66-292212181ae0

import Definitions.Def_DerivativeChainPrivate_foundations
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_chain_strict
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 0
set_option maxRecDepth 100000


section
-- Source module: VerifiedCube

open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate

theorem derivative_root_norm_le {P : Polynomial ℂ} (hP : 0 < P.degree)
    (R : ℝ) (hR : ∀ w ∈ P.roots, ‖w‖ ≤ R) {z : ℂ}
    (hz : P.derivative.eval z = 0) : ‖z‖ ≤ R := by
  have hp : P ≠ 0 := by rintro rfl; simp at hP
  have hd : P.derivative ≠ 0 := Polynomial.derivative_eq_zero.not.mpr
    (Nat.ne_of_gt (Polynomial.natDegree_pos_iff_degree_pos.mpr hP))
  have hm : z ∈ P.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hz⟩
  have hs : P.rootSet ℂ ⊆ Metric.closedBall (0 : ℂ) R := by
    intro w hw
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
    simpa only [Metric.mem_closedBall, dist_zero_right] using
      hR w ((Polynomial.mem_roots hp).mpr hw.2)
  have hmem := (convexHull_min hs (convex_closedBall (0 : ℂ) R))
    (P.rootSet_derivative_subset_convexHull_rootSet hP hm)
  simpa only [Metric.mem_closedBall, dist_zero_right] using hmem







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







theorem chainCost_eq_sum_range {n : ℕ} (f : ℕ → ℂ) :
    chainCost (fun i : Fin n => f i.val) =
      ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ := by
  unfold chainCost
  exact Fin.sum_univ_eq_sum_range (fun i => ‖f (i + 1) - f i‖) (n - 1)



theorem chainCost_translate {n : ℕ} (z : Fin n → ℂ) (u : ℂ) :
    chainCost (fun i => z i + u) = chainCost z := by
  simp only [chainCost, add_sub_add_right_eq_sub]

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
open scoped BigOperators
namespace DerivativeChainPrivate

theorem polynomial_eval_tendsto_of_coeff (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (N : ℕ) (hp : ∀ j, (p j).natDegree ≤ N) (hq : q.natDegree ≤ N)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → ℂ) (w : ℂ) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun j => (p j).eval (z j)) atTop (𝓝 (q.eval w)) := by
  have heval (j : ℕ) : (p j).eval (z j) =
      ∑ k ∈ Finset.range (N + 1), (p j).coeff k * (z j) ^ k :=
    Polynomial.eval_eq_sum_range' (by have := hp j; omega) _
  have hqeval : q.eval w = ∑ k ∈ Finset.range (N + 1), q.coeff k * w ^ k :=
    Polynomial.eval_eq_sum_range' (by omega) _
  rw [hqeval]
  have hs : Tendsto (fun j => ∑ k ∈ Finset.range (N + 1), (p j).coeff k * (z j) ^ k)
      atTop (𝓝 (∑ k ∈ Finset.range (N + 1), q.coeff k * w ^ k)) :=
    tendsto_finsetSum _ (fun k _ => (hc k).mul (hz.pow k))
  exact hs.congr' (Eventually.of_forall (fun j => (heval j).symm))

theorem iterate_derivative_eval_tendsto (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (N : ℕ) (hp : ∀ j, (p j).natDegree ≤ N) (hq : q.natDegree ≤ N)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (k : ℕ) (z : ℕ → ℂ) (w : ℂ) (hz : Tendsto z atTop (𝓝 w)) :
    Tendsto (fun j => (Polynomial.derivative^[k] (p j)).eval (z j))
      atTop (𝓝 ((Polynomial.derivative^[k] q).eval w)) := by
  apply polynomial_eval_tendsto_of_coeff _ _ N
    (fun j => (Polynomial.natDegree_iterate_derivative (p j) k).trans
      ((Nat.sub_le _ _).trans (hp j)))
    ((Polynomial.natDegree_iterate_derivative q k).trans ((Nat.sub_le _ _).trans hq)) _ z w hz
  intro m
  simp only [Polynomial.coeff_iterate_derivative, nsmul_eq_mul]
  exact tendsto_const_nhds.mul (hc (m + k))



end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate

theorem northeast_chain_cost (n : ℕ) (z : ℕ → ℂ)
    (hre : ∀ i < n - 1, (z i).re ≤ (z (i + 1)).re)
    (him : ∀ i < n - 1, (z i).im ≤ (z (i + 1)).im) :
    chainCost (fun i : Fin n => z i.val) ≤
      Real.sqrt 2 * ‖z (n - 1) - z 0‖ := by
  have hstep (i : ℕ) (hi : i < n - 1) :
      ‖z (i + 1) - z i‖ ≤
        ((z (i + 1)).re - (z i).re) + ((z (i + 1)).im - (z i).im) := by
    simpa only [Complex.sub_re, Complex.sub_im,
      abs_of_nonneg (sub_nonneg.mpr (hre i hi)),
      abs_of_nonneg (sub_nonneg.mpr (him i hi))] using
      Complex.norm_le_abs_re_add_abs_im (z (i + 1) - z i)
  have hsum : chainCost (fun i : Fin n => z i.val) ≤
      ((z (n - 1)).re - (z 0).re) + ((z (n - 1)).im - (z 0).im) := by
    rw [chainCost_eq_sum_range]
    calc
      _ ≤ ∑ i ∈ Finset.range (n - 1),
          (((z (i + 1)).re - (z i).re) + ((z (i + 1)).im - (z i).im)) :=
        Finset.sum_le_sum fun i hi => hstep i (Finset.mem_range.mp hi)
      _ = _ := by rw [Finset.sum_add_distrib,
          Finset.sum_range_sub (fun i => (z i).re),
          Finset.sum_range_sub (fun i => (z i).im)]
  apply hsum.trans
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Complex.sq_norm (z (n - 1) - z 0)
  have hdiff := sq_nonneg (((z (n - 1)).re - (z 0).re) -
    ((z (n - 1)).im - (z 0).im))
  rw [Complex.normSq_apply] at hn
  simp only [Complex.sub_re, Complex.sub_im] at hn
  have hp := mul_nonneg (Real.sqrt_nonneg 2) (norm_nonneg (z (n - 1) - z 0))
  nlinarith only [hs, hn, hdiff, hp]

theorem cubic_root_centroid_radius (u v w o : ℂ) (R : ℝ)
    (hu : ‖u - o‖ ≤ R) (hv : ‖v - o‖ ≤ R) (hw : ‖w - o‖ ≤ R) :
    ‖u - (u + v + w) / 3‖ ≤ 4 * R / 3 := by
  have heq : u - (u + v + w) / 3 =
      (2 * (u - o) - (v - o) - (w - o)) / 3 := by ring
  rw [heq, norm_div]
  have htwo : ‖(2 : ℂ) * (u - o)‖ = 2 * ‖u - o‖ := by
    rw [norm_mul]; norm_num
  have h1 := norm_sub_le ((2 : ℂ) * (u - o)) (v - o)
  have h2 := norm_sub_le ((2 : ℂ) * (u - o) - (v - o)) (w - o)
  rw [htwo] at h1
  norm_num only [Complex.norm_ofNat]
  linarith

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

theorem affine_orthonormal_coordinates {n : ℕ} (z : Fin n → ℂ) (a b t c : ℂ)
    (hc : c ≠ 0) (ha : ‖a‖ = 1) (hb : ‖b‖ = 1)
    (hab : (a*starRingEnd ℂ b).re = 0)
    (hmonoA : Monotone (fun i => (a*z i).re))
    (hmonoB : Monotone (fun i => (b*z i).re)) :
    ∃ A B : ℂ, ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ (A*starRingEnd ℂ B).re = 0 ∧
      Monotone (fun i => (A*(t+c*z i)).re) ∧ Monotone (fun i => (B*(t+c*z i)).re) := by
  let d := starRingEnd ℂ c/(‖c‖ : ℂ)
  have hcn : 0 < ‖c‖ := norm_pos_iff.mpr hc
  have hcast : (‖c‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr hcn.ne'
  have hdn : ‖d‖ = 1 := by
    dsimp only [d]
    rw [norm_div,Complex.norm_conj,Complex.norm_real,Real.norm_eq_abs,abs_of_pos hcn,div_self hcn.ne']
  have hdc : d*c = (‖c‖ : ℂ) := by
    dsimp only [d]
    rw [div_mul_eq_mul_div,mul_comm (starRingEnd ℂ c) c,Complex.mul_conj,←Complex.sq_norm,Complex.ofReal_pow]
    field_simp
  have hdd : d*starRingEnd ℂ d = 1 := by
    rw [Complex.mul_conj,←Complex.sq_norm,hdn]
    norm_num
  have horth : ((a*d)*starRingEnd ℂ (b*d)).re = 0 := by
    have heq : (a*d)*starRingEnd ℂ (b*d) = (a*starRingEnd ℂ b)*(d*starRingEnd ℂ d) := by
      rw [map_mul]
      ring
    rw [heq,hdd,mul_one]
    exact hab
  have hcoord (u : ℂ) (i : Fin n) : ((u*d)*(t+c*z i)).re =
      ((u*d)*t).re+‖c‖*(u*z i).re := by
    have heq : (u*d)*(t+c*z i) = (u*d)*t+(‖c‖ : ℂ)*(u*z i) := by
      calc
        _ = (u*d)*t+(d*c)*(u*z i) := by ring
        _ = _ := by rw [hdc]
    rw [heq]
    simp only [Complex.add_re,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
  refine ⟨a*d,b*d,by simp only [norm_mul,ha,hdn,mul_one],
    by simp only [norm_mul,hb,hdn,mul_one],horth,?_,?_⟩
  · intro i j hij
    change (a*d*(t+c*z i)).re ≤ (a*d*(t+c*z j)).re
    rw [hcoord,hcoord]
    have h := mul_le_mul_of_nonneg_left (hmonoA hij) hcn.le
    linarith only [h]
  · intro i j hij
    change (b*d*(t+c*z i)).re ≤ (b*d*(t+c*z j)).re
    rw [hcoord,hcoord]
    have h := mul_le_mul_of_nonneg_left (hmonoB hij) hcn.le
    linarith only [h]

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



theorem iterate_derivative_norm_bound (p : Polynomial ℂ) (k : ℕ) (hk : k < p.natDegree)
    (M : ℝ) (hbound : ∀ z, p.eval z = 0 → ‖z‖ ≤ M) (z : ℂ)
    (hz : (derivative^[k] p).eval z = 0) : ‖z‖ ≤ M := by
  induction k generalizing p with
  | zero => exact hbound z hz
  | succ k ih =>
    have hkd : k < p.derivative.natDegree := by rw [natDegree_derivative]; omega
    have hpne : p ≠ 0 := by intro h; simp [h] at hk
    have hpd : 0 < p.degree := natDegree_pos_iff_degree_pos.mp (by omega)
    have hdbound : ∀ w, p.derivative.eval w = 0 → ‖w‖ ≤ M := by
      intro w hw
      exact derivative_root_norm_le hpd M
        (fun z hz => hbound z ((mem_roots hpne).mp hz)) hw
    rw [Function.iterate_succ_apply] at hz
    exact ih p.derivative hkd hdbound hz

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

theorem cubic_perturbation_disk (u v w o a : ℂ) (R t : ℝ) (ht : 0 ≤ t)
    (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R) :
    ‖u+(t : ℂ)*a-o‖ ≤ R+t*‖a‖ ∧
      ‖v-(t : ℂ)*a/2-o‖ ≤ R+t*‖a‖ ∧ ‖w-(t : ℂ)*a/2-o‖ ≤ R+t*‖a‖ := by
  have hn : ‖(t : ℂ)*a‖ = t*‖a‖ := by
    rw [norm_mul,Complex.norm_real,Real.norm_eq_abs,abs_of_nonneg ht]
  have hpert (x : ℂ) (hx : ‖x-o‖ ≤ R) : ‖x-(t : ℂ)*a/2-o‖ ≤ R+t*‖a‖ := by
    have heq : x-(t : ℂ)*a/2-o = (x-o)-(t : ℂ)*a/2 := by ring
    rw [heq]
    have h := norm_sub_le (x-o) ((t : ℂ)*a/2)
    rw [norm_div,hn] at h
    norm_num only [Complex.norm_ofNat] at h
    nlinarith only [h,hx,mul_nonneg ht (norm_nonneg a)]
  refine ⟨?_,hpert v hv,hpert w hw⟩
  have heq : u+(t : ℂ)*a-o = (u-o)+(t : ℂ)*a := by ring
  rw [heq]
  have h := norm_add_le (u-o) ((t : ℂ)*a)
  rw [hn] at h
  linarith only [h,hu]

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



end


section
-- Source module: FrameLimits


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate

theorem framed_power_chain_collision_limit (n k : ℕ) [NeZero n] (last : Fin n) (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (a b : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j i, ‖z j i‖ ≤ M)
    (hroot : ∀ j i, (Polynomial.derivative^[n-(i.val+1)] (p j)).eval (z j i) = 0)
    (η : ℂ) (hstart : ∀ j, z j 0 = η)
    (htail : ∀ j i, k ≤ i.val → z j i = z j last)
    (ha : ∀ j, ‖a j‖ = 1) (hb : ∀ j, ‖b j‖ = 1)
    (hab : ∀ j, (a j*starRingEnd ℂ (b j)).re = 0)
    (hmonoA : ∀ j, Monotone (fun i => (a j*z j i).re))
    (hmonoB : ∀ j, Monotone (fun i => (b j*z j i).re))
    (c : ℕ → ℝ) (C : ℝ) (hcLim : Tendsto c atTop (𝓝 C))
    (hcost : ∀ j, chainCost (z j) ≤ c j) :
    ∃ (w : Fin n → ℂ) (A B : ℂ),
      (∀ i, (Polynomial.derivative^[n-(i.val+1)] q).eval (w i) = 0) ∧
      w 0 = η ∧ (∀ i : Fin n, k ≤ i.val → w i = w last) ∧
      ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ (A*starRingEnd ℂ B).re = 0 ∧
      Monotone (fun i => (A*w i).re) ∧ Monotone (fun i => (B*w i).re) ∧ chainCost w ≤ C := by
  let packed (j : ℕ) : ((Fin n → ℂ) × ℂ) × ℂ := ((z j,a j),b j)
  let S := max M 1
  have hS : 0 ≤ S := le_trans (by norm_num) (le_max_right M 1)
  have hmem (j : ℕ) : packed j ∈ Metric.closedBall 0 S := by
    rw [Metric.mem_closedBall,dist_zero_right]
    change max (max ‖z j‖ ‖a j‖) ‖b j‖ ≤ S
    have hzNorm : ‖z j‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr (hbound j)
    exact max_le (max_le (hzNorm.trans (le_max_left M 1))
      (by rw [ha]; exact le_max_right M 1)) (by rw [hb]; exact le_max_right M 1)
  obtain ⟨u,_,φ,hφ,hlim⟩ := (isCompact_closedBall (0 : ((Fin n → ℂ) × ℂ) × ℂ) S).isSeqCompact hmem
  let w := u.1.1
  let A := u.1.2
  let B := u.2
  have hφlim := hφ.tendsto_atTop
  have hzlim : Tendsto (fun j => z (φ j)) atTop (𝓝 w) := by
    have hc : Continuous (fun p : ((Fin n → ℂ) × ℂ) × ℂ => p.1.1) := continuous_fst.fst
    simpa only [Function.comp_def,packed,w] using hc.continuousAt.tendsto.comp hlim
  have hAlim : Tendsto (fun j => a (φ j)) atTop (𝓝 A) := by
    have hc : Continuous (fun p : ((Fin n → ℂ) × ℂ) × ℂ => p.1.2) := continuous_fst.snd
    simpa only [Function.comp_def,packed,A] using hc.continuousAt.tendsto.comp hlim
  have hBlim : Tendsto (fun j => b (φ j)) atTop (𝓝 B) := by
    have hc : Continuous (fun p : ((Fin n → ℂ) × ℂ) × ℂ => p.2) := continuous_snd
    simpa only [Function.comp_def,packed,B] using hc.continuousAt.tendsto.comp hlim
  have hcoord (i : Fin n) : Tendsto (fun j => z (φ j) i) atTop (𝓝 (w i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hzlim
  refine ⟨w,A,B,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    have hrootlim := iterate_derivative_eval_tendsto (fun j => p (φ j)) q n
      (fun j => hp (φ j)) hq (fun k => (hc k).comp hφlim)
      (n-(i.val+1)) (fun j => z (φ j) i) (w i) (hcoord i)
    exact tendsto_nhds_unique hrootlim (by
      simpa only [hroot] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  · exact tendsto_nhds_unique (hcoord 0) (by
      simpa only [hstart] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => η) atTop (𝓝 η)))
  · intro i hi
    have h := hcoord i
    have heq : (fun j => z (φ j) i) = (fun j => z (φ j) last) :=
      funext (fun j => htail (φ j) i hi)
    rw [heq] at h
    exact tendsto_nhds_unique h (hcoord last)
  · exact tendsto_nhds_unique (continuous_norm.continuousAt.tendsto.comp hAlim) (by
      simpa only [Function.comp_def,ha] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  · exact tendsto_nhds_unique (continuous_norm.continuousAt.tendsto.comp hBlim) (by
      simpa only [Function.comp_def,hb] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (1 : ℝ)) atTop (𝓝 1)))
  · have horthlim := Complex.continuous_re.continuousAt.tendsto.comp
      (hAlim.mul (Complex.continuous_conj.continuousAt.tendsto.comp hBlim))
    exact tendsto_nhds_unique horthlim (by
      simpa only [Function.comp_def,hab] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℝ)) atTop (𝓝 0)))
  · intro i j hij
    exact le_of_tendsto_of_tendsto
      (Complex.continuous_re.continuousAt.tendsto.comp (hAlim.mul (hcoord i)))
      (Complex.continuous_re.continuousAt.tendsto.comp (hAlim.mul (hcoord j)))
      (Eventually.of_forall (fun s => hmonoA (φ s) hij))
  · intro i j hij
    exact le_of_tendsto_of_tendsto
      (Complex.continuous_re.continuousAt.tendsto.comp (hBlim.mul (hcoord i)))
      (Complex.continuous_re.continuousAt.tendsto.comp (hBlim.mul (hcoord j)))
      (Eventually.of_forall (fun s => hmonoB (φ s) hij))
  · have hcontinuous : Continuous (fun v : Fin n → ℂ => chainCost v) := by
      unfold chainCost
      fun_prop
    exact le_of_tendsto_of_tendsto (hcontinuous.continuousAt.tendsto.comp hzlim)
      (hcLim.comp hφlim) (Eventually.of_forall (fun j => hcost (φ j)))

end DerivativeChainPrivate

end


section
-- Source module: CoordinateLimits


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate

theorem coordinate_chain_collision_limit (n k : ℕ) [NeZero n] (last : Fin n)
    (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ n) (hq : q.natDegree ≤ n)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin n → ℂ) (M : ℝ) (hM : 0 ≤ M) (hbound : ∀ j i, ‖z j i‖ ≤ M)
    (hroot : ∀ j i, (Polynomial.derivative^[n-(i.val+1)] (p j)).eval (z j i)=0)
    (η : ℂ) (hstart : ∀ j, z j 0=η)
    (htail : ∀ j i, k ≤ i.val → z j i=z j last)
    (hmonoR : ∀ j, Monotone (fun i => (z j i).re))
    (hmonoI : ∀ j, Monotone (fun i => (z j i).im)) :
    ∃ w : Fin n → ℂ,
      (∀ i, (Polynomial.derivative^[n-(i.val+1)] q).eval (w i)=0) ∧
      w 0=η ∧ (∀ i : Fin n, k ≤ i.val → w i=w last) ∧
      Monotone (fun i => (w i).re) ∧ Monotone (fun i => (w i).im) := by
  have hmem (j : ℕ) : z j ∈ Metric.closedBall (0:Fin n → ℂ) M := by
    rw [Metric.mem_closedBall,dist_zero_right]
    exact (pi_norm_le_iff_of_nonneg hM).mpr (hbound j)
  obtain ⟨w,_,φ,hφ,hlim⟩ := (isCompact_closedBall (0:Fin n → ℂ) M).isSeqCompact hmem
  have hφlim := hφ.tendsto_atTop
  have hcoord (i : Fin n) : Tendsto (fun j => z (φ j) i) atTop (𝓝 (w i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hlim
  refine ⟨w,?_,?_,?_,?_,?_⟩
  · intro i
    have hh := iterate_derivative_eval_tendsto (fun j => p (φ j)) q n
      (fun j => hp (φ j)) hq (fun k => (hc k).comp hφlim)
      (n-(i.val+1)) (fun j => z (φ j) i) (w i) (hcoord i)
    exact tendsto_nhds_unique hh (by simpa only [hroot] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0:ℂ)) atTop (𝓝 0)))
  · exact tendsto_nhds_unique (hcoord 0) (by simpa only [hstart] using
      (tendsto_const_nhds : Tendsto (fun _ : ℕ => η) atTop (𝓝 η)))
  · intro i hi
    have hh := hcoord i
    have he : (fun j => z (φ j) i) = (fun j => z (φ j) last) := funext (fun j => htail (φ j) i hi)
    rw [he] at hh
    exact tendsto_nhds_unique hh (hcoord last)
  · intro i j hij
    exact le_of_tendsto_of_tendsto
      (Complex.continuous_re.continuousAt.tendsto.comp (hcoord i))
      (Complex.continuous_re.continuousAt.tendsto.comp (hcoord j))
      (Eventually.of_forall (fun t => hmonoR (φ t) hij))
  · intro i j hij
    exact le_of_tendsto_of_tendsto
      (Complex.continuous_im.continuousAt.tendsto.comp (hcoord i))
      (Complex.continuous_im.continuousAt.tendsto.comp (hcoord j))
      (Eventually.of_forall (fun t => hmonoI (φ t) hij))

theorem finite_coordinate_chain_cost (n : ℕ) [NeZero n] (z : Fin n → ℂ) (last : Fin n)
    (hlast : last.val=n-1) (hre : Monotone (fun i => (z i).re))
    (him : Monotone (fun i => (z i).im)) :
    chainCost z ≤ Real.sqrt 2*‖z last-z 0‖ := by
  have hn : 0 < n := Nat.pos_of_ne_zero (NeZero.ne n)
  let g : ℕ → ℂ := fun i => if hi : i < n then z ⟨i,hi⟩ else 0
  have hR : ∀ i < n-1, (g i).re ≤ (g (i+1)).re := by
    intro i hi
    have hi0 : i < n := by omega
    have hi1 : i+1 < n := by omega
    simp only [g,dif_pos hi0,dif_pos hi1]
    exact hre (show (⟨i,hi0⟩:Fin n) ≤ ⟨i+1,hi1⟩ from Nat.le_succ i)
  have hI : ∀ i < n-1, (g i).im ≤ (g (i+1)).im := by
    intro i hi
    have hi0 : i < n := by omega
    have hi1 : i+1 < n := by omega
    simp only [g,dif_pos hi0,dif_pos hi1]
    exact him (show (⟨i,hi0⟩:Fin n) ≤ ⟨i+1,hi1⟩ from Nat.le_succ i)
  have hh := northeast_chain_cost n g hR hI
  have hfun : (fun i : Fin n => g i.val)=z := by funext i; simp [g,i.isLt]
  rw [hfun] at hh
  have hl : n-1 < n := by omega
  have he : (⟨n-1,hl⟩:Fin n)=last := Fin.ext hlast.symm
  have hzero : (⟨0,hn⟩:Fin n)=0 := by apply Fin.ext; simp
  simpa only [g,dif_pos hl,dif_pos hn,he,hzero] using hh

end DerivativeChainPrivate

end


section
-- Source module: NormalizedBoundary


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

theorem normalized_power_chain_boundary (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
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
  obtain ⟨w,hwroot,hwstart,hwtail,hwR,hwI⟩ := coordinate_chain_collision_limit (3*h) (2*h) last P ((q β)^h)
    (fun j => (hdegree (γ j)).le) (hdegree β).le hPcoeff z M hM hbound hzroot 0 hzstart hztail hzmonoR hzmonoI
  have hend : (q β).eval (w last)=0 := by
    have hr := hwroot last
    have hk : 3*h-(last.val+1)=0 := by omega
    rw [hk,Function.iterate_zero_apply,eval_pow] at hr
    exact (pow_eq_zero_iff (Nat.ne_of_gt hh)).mp hr
  refine ⟨w,hwroot,hwstart,hwtail,hend,hwR,hwI,?_⟩
  have hc := finite_coordinate_chain_cost (3*h) w last hlast hwR hwI
  simpa only [hwstart,sub_zero] using hc

end DerivativeChainPrivate

end


section
-- Source module: NormalizedFrames


set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_power_chain_frame (h : ℕ) [NeZero (3*h)] (a b : ℝ) (last : Fin (3*h))
    (hupper : ∀ β : ℂ, 0 ≤ β.re → 0 ≤ β.im → ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval (z last)=0 ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2*‖z last‖)
    (β : ℂ) (hR : 0 ≤ β.re) :
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ Real.sqrt 2*‖z last‖ := by
  by_cases hI : 0 ≤ β.im
  · obtain ⟨z,hroot,hstart,htail,hend,hre,him,hcost⟩ := hupper β hR hI
    refine ⟨z,1,-Complex.I,hroot,hstart,htail,hend,by simp,by simp,by simp,?_,?_,hcost⟩
    · simpa only [one_mul] using hre
    · simpa [Complex.mul_re] using him
  · let γ := starRingEnd ℂ β
    have hγR : 0 ≤ γ.re := by simpa only [γ,Complex.conj_re] using hR
    have hγI : 0 ≤ γ.im := by dsimp only [γ]; rw [Complex.conj_im]; linarith
    obtain ⟨z,hroot,hstart,htail,hend,hre,him,hcost⟩ := hupper γ hγR hγI
    let f : Fin (3*h) → ℂ := fun i => starRingEnd ℂ (z i)
    have hmap : (((X^3-C (a:ℂ)*X-C ((b:ℂ)*γ))^h : Polynomial ℂ)).map (starRingEnd ℂ) =
        (X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h := by simp [γ]
    have hmapq : ((X^3-C (a:ℂ)*X-C ((b:ℂ)*γ)):Polynomial ℂ).map (starRingEnd ℂ) =
        X^3-C (a:ℂ)*X-C ((b:ℂ)*β) := by simp [γ]
    have hroots (i : Fin (3*h)) :
        (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (f i)=0 := by
      rw [← hmap,conjugate_derivative_eval,hroot,map_zero]
    refine ⟨f,1,Complex.I,hroots,?_,?_,?_,by simp,by simp,by simp,?_,?_,?_⟩
    · simpa only [f,hstart,map_zero]
    · intro i hi
      exact congrArg (starRingEnd ℂ) (htail i hi)
    · rw [← hmapq]
      change (derivative^[0] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*γ)).map (starRingEnd ℂ))).eval (starRingEnd ℂ (z last))=0
      rw [conjugate_derivative_eval]
      simpa using congrArg (starRingEnd ℂ) hend
    · simpa only [f,one_mul,Complex.conj_re] using hre
    · simpa [f,Complex.mul_re] using him
    · simpa only [f,chainCost_conjugate,Complex.norm_conj] using hcost

end DerivativeChainPrivate

end


section
-- Source module: PowerNormalization


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem cubic_triple_normalization_parameters (u v w : ℂ) (a b : ℝ) (ha : 0 < a) (hb : 0 < b)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0) :
    ∃ c β : ℂ, c ≠ 0 ∧ 0 ≤ β.re ∧
      ((X-C u)*(X-C v)*(X-C w)).comp (C ((u+v+w)/3)+C c*X) =
        C (c^3)*(X^3-C (a:ℂ)*X-C ((b:ℂ)*β)) := by
  let η := (u+v+w)/3
  let A := (u^2+v^2+w^2-u*v-u*w-v*w)/3
  let B := (u-η)*(v-η)*(w-η)
  have haC : (a:ℂ) ≠ 0 := by exact_mod_cast ha.ne'
  have hbC : (b:ℂ) ≠ 0 := by exact_mod_cast hb.ne'
  have hdepress (t : ℂ) : (η+t-u)*(η+t-v)*(η+t-w)=t^3-A*t-B := by dsimp [η,A,B]; ring
  obtain ⟨c,hc2⟩ := IsAlgClosed.exists_pow_nat_eq (A/(a:ℂ)) (show 0 < 2 by norm_num)
  have hAc : A=(a:ℂ)*c^2 := by rw [hc2]; field_simp
  have hc : c ≠ 0 := by
    intro he
    apply hA
    change A=0
    simpa [he] using hAc
  have hcomp (c : ℂ) (hc : c ≠ 0) (hc2 : c^2=A/(a:ℂ)) :
      ((X-C u)*(X-C v)*(X-C w)).comp (C η+C c*X) =
        C (c^3)*(X^3-C (a:ℂ)*X-C ((b:ℂ)*(B/((b:ℂ)*c^3)))) := by
    have hAc : A=(a:ℂ)*c^2 := by rw [hc2]; field_simp
    apply Polynomial.funext
    intro z
    simp only [eval_comp,eval_mul,eval_C,eval_add,eval_X,eval_sub,eval_pow,eval_ofNat]
    rw [hdepress (c*z),hAc]
    field_simp
  by_cases hβ : 0 ≤ (B/((b:ℂ)*c^3)).re
  · exact ⟨c,B/((b:ℂ)*c^3),hc,hβ,hcomp c hc hc2⟩
  · have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
    have hc2' : (-c)^2=A/(a:ℂ) := by simpa only [neg_sq] using hc2
    have hneg : B/((b:ℂ)*(-c)^3)=-(B/((b:ℂ)*c^3)) := by
      rw [show (-c)^3=-(c^3) by ring,mul_neg,div_neg]
    refine ⟨-c,B/((b:ℂ)*(-c)^3),hc',?_,hcomp (-c) hc' hc2'⟩
    rw [hneg,Complex.neg_re]
    linarith

end DerivativeChainPrivate

end


section
-- Source module: PowerNonzeroMoment


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem cubic_power_nonzero_moment_chain (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (last : Fin (3*h))
    (hframe : ∀ β : ℂ, 0 ≤ β.re → ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)).eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ Real.sqrt 2*‖z last‖)
    (u v w o : ℂ) (R : ℝ) (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0) :
    let q := (X-C u)*(X-C v)*(X-C w)
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
      z 0=(u+v+w)/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ 4*Real.sqrt 2*R/3 := by
  let q : Polynomial ℂ := (X-C u)*(X-C v)*(X-C w)
  let η := (u+v+w)/3
  obtain ⟨c,β,hc,hβ,hcomp⟩ := cubic_triple_normalization_parameters u v w a b ha hb hA
  obtain ⟨g,A,B,hroots,hstart,htail,hend,hAunit,hBunit,horth,hmonoA,hmonoB,hcost⟩ := hframe β hβ
  let f : Fin (3*h) → ℂ := fun i => η+c*g i
  have hpower : (q^h).comp (C η+C c*X) =
      C (c^(3*h))*(X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h := by
    rw [pow_comp,hcomp,mul_pow,← C_pow,← pow_mul]
  have hfroot (i : Fin (3*h)) : (derivative^[3*h-(i.val+1)] (q^h)).eval (f i)=0 :=
    affine_derivative_root (q^h) ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h) η c (c^(3*h)) hc hpower _ (g i) (hroots i)
  have hqend : q.eval (f last)=0 :=
    affine_derivative_root q (X^3-C (a:ℂ)*X-C ((b:ℂ)*β)) η c (c^3) hc hcomp 0 (g last) hend
  have hcenter : ‖f last-η‖ ≤ 4*R/3 := by
    have ht := hqend
    simp only [q,eval_mul,eval_sub,eval_X,eval_C] at ht
    rcases mul_eq_zero.mp ht with huv|hw'
    · rcases mul_eq_zero.mp huv with hu'|hv'
      · rw [sub_eq_zero.mp hu']
        exact cubic_root_centroid_radius u v w o R hu hv hw
      · rw [sub_eq_zero.mp hv']
        have hη : (v+u+w)/3=η := by dsimp [η]; ring
        simpa only [hη] using cubic_root_centroid_radius v u w o R hv hu hw
    · rw [sub_eq_zero.mp hw']
      have hη : (w+u+v)/3=η := by dsimp [η]; ring
      simpa only [hη] using cubic_root_centroid_radius w u v o R hw hu hv
  have hfcost : chainCost f ≤ 4*Real.sqrt 2*R/3 := by
    rw [chainCost_affine]
    calc
      _ ≤ ‖c‖*(Real.sqrt 2*‖g last‖) := mul_le_mul_of_nonneg_left hcost (norm_nonneg c)
      _ = Real.sqrt 2*‖f last-η‖ := by dsimp only [f]; rw [add_sub_cancel_left,norm_mul]; ring
      _ ≤ Real.sqrt 2*(4*R/3) := mul_le_mul_of_nonneg_left hcenter (Real.sqrt_nonneg 2)
      _ = _ := by ring
  obtain ⟨A',B',hA',hB',horth',hmA,hmB⟩ :=
    affine_orthonormal_coordinates g A B η c hc hAunit hBunit horth hmonoA hmonoB
  refine ⟨f,A',B',hfroot,?_,?_,hqend,hA',hB',horth',hmA,hmB,hfcost⟩
  · simp only [f,hstart,mul_zero,add_zero,η]
  · intro i hi
    exact congrArg (fun t => η+c*t) (htail i hi)

end DerivativeChainPrivate

end


section
-- Source module: PowerZeroMoment


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

theorem cubic_power_zero_moment_chain (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hnonzero : ∀ u v w o : ℂ, ∀ R : ℝ, ‖u-o‖ ≤ R → ‖v-o‖ ≤ R → ‖w-o‖ ≤ R →
      (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0 →
      let q := (X-C u)*(X-C v)*(X-C w)
      ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
        (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
        z 0=(u+v+w)/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
        ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
        Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
        chainCost z ≤ 4*Real.sqrt 2*R/3)
    (u v w o : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3=0) :
    let q := (X-C u)*(X-C v)*(X-C w)
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
      z 0=(u+v+w)/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ 4*Real.sqrt 2*R/3 := by
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
      positivity
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
    let costs (j : ℕ) := 4*Real.sqrt 2*r j/3
    have hrLim : Tendsto r atTop (𝓝 R) := by
      simpa only [r,zero_mul,add_zero] using
        (tendsto_const_nhds (x:=R)).add (hεlim.mul (tendsto_const_nhds (x:=‖d‖)))
    have hCLim : Tendsto costs atTop (𝓝 (4*Real.sqrt 2*R/3)) :=
      ((tendsto_const_nhds (x:=4*Real.sqrt 2)).mul hrLim).div_const 3
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

end DerivativeChainPrivate

end


section
-- Source module: PowerRadius


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem cubic_power_radius_of_strict_normalized_chain (h : ℕ) (hh : 0 < h) [NeZero (3*h)]
    (a b : ℝ) (ha : 0 < a) (hb : 0 < b) (last : Fin (3*h)) (hlast : last.val=3*h-1)
    (hstrict : ∀ β : ℂ, 0 ≤ β.re → 0 < β.im → ∃ z : Fin (3*h) → ℂ,
      (∀ i, (derivative^[3*h-(i.val+1)] ((X^3-C (a:ℂ)*X-C ((b:ℂ)*β))^h)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im))
    (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree=3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x=0 → ‖x-o‖ ≤ R) :
    ∃ (z : Fin (3*h) → ℂ) (A B : ℂ),
      (∀ i, (derivative^[3*h-(i.val+1)] (q^h)).eval (z i)=0) ∧
      z 0=q.roots.sum/3 ∧ (∀ i : Fin (3*h), 2*h ≤ i.val → z i=z last) ∧ q.eval (z last)=0 ∧
      ‖A‖=1 ∧ ‖B‖=1 ∧ (A*starRingEnd ℂ B).re=0 ∧
      Monotone (fun i => (A*z i).re) ∧ Monotone (fun i => (B*z i).re) ∧
      chainCost z ≤ 4*Real.sqrt 2*R/3 := by
  classical
  have hupper := normalized_power_chain_boundary h hh a b ha.le hb.le last hlast hstrict
  have hframe := normalized_power_chain_frame h a b last hupper
  have hnonzero := cubic_power_nonzero_moment_chain h hh a b ha hb last hframe
  have hcard : q.roots.card=3 := by rw [← (IsAlgClosed.splits q).natDegree_eq_card_roots,hdeg]
  obtain ⟨u,v,w,hroots⟩ := Multiset.card_eq_three.mp hcard
  have hfactor : q=(X-C u)*(X-C v)*(X-C w) := by
    rw [(IsAlgClosed.splits q).eq_prod_roots_of_monic hq,hroots]
    simp [mul_assoc]
  have hu : ‖u-o‖ ≤ R := hbound u ((mem_roots hq.ne_zero).mp (by rw [hroots]; simp))
  have hv : ‖v-o‖ ≤ R := hbound v ((mem_roots hq.ne_zero).mp (by rw [hroots]; simp))
  have hw : ‖w-o‖ ≤ R := hbound w ((mem_roots hq.ne_zero).mp (by rw [hroots]; simp))
  have hsol := if hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0 then
      hnonzero u v w o R hu hv hw hA
    else cubic_power_zero_moment_chain h hh last hlast hnonzero u v w o R hR hu hv hw (by simpa using hA)
  obtain ⟨z,A,B,hzroot,hstart,htail,hend,hA,hB,horth,hmA,hmB,hcost⟩ := hsol
  refine ⟨z,A,B,?_,?_,htail,?_,hA,hB,horth,hmA,hmB,hcost⟩
  · simpa only [hfactor] using hzroot
  · simpa [hroots,add_assoc] using hstart
  · simpa only [hfactor] using hend

end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree = 3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x = 0 → ‖x - o‖ ≤ R) :
    ∃ (z : Fin 15 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[15 - (i.val + 1)] (q^5)).eval (z i) = 0) ∧
      z 0 = q.roots.sum / 3 ∧
      (∀ i : Fin 15, 10 ≤ i.val → z i = z 14) ∧ q.eval (z 14) = 0 ∧
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a * starRingEnd ℂ b).re = 0 ∧
      Monotone (fun i => (a * z i).re) ∧ Monotone (fun i => (b * z i).re) ∧
      chainCost z ≤ 4 * Real.sqrt 2 * R / 3 := by
  apply cubic_power_radius_of_strict_normalized_chain 5 (by norm_num) 7 91
    (by norm_num) (by norm_num) 14 (by rfl) _ q hq hdeg o R hR hbound
  intro β hβR hβI
  obtain ⟨z,hroots,hstart,htail,_,hmR,hmI,_⟩ := normalized_fifth_chain_strict β hβR hβI
  refine ⟨z,?_,hstart,htail,hmR,hmI⟩
  intro i
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,C_mul,C_ofNat] using hroots i
