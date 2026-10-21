-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_fifth_chain_strict
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T23:14:55.952834+00:00
-- url     : https://prove2.me/submissions/8d9f9a52-b941-45e1-8291-bdd8c5232188

import Definitions.Def_DerivativeChainPrivate_fifth_power_inverse_certificates
import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_decic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_nonic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_octic_step_with_bounds
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_selected_sextic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_septic_step_with_bounds
import Theorems.Thm_DerivativeChainPrivate_normalized_fifth_source_step
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









end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem derivative_supporting_parent (p : Polynomial ℂ) (hdegree : 2 ≤ p.natDegree)
    (z : ℂ) (hz : p.derivative.eval z = 0) :
    ∃ w : ℂ, p.eval w = 0 ∧ ‖z‖ ^ 2 ≤ (w * starRingEnd ℂ z).re := by
  have hp : p ≠ 0 := by intro h; simp [h] at hdegree
  have hd : p.derivative ≠ 0 := by
    intro h; have hh := Polynomial.derivative_eq_zero.mp h; omega
  have hzset : z ∈ p.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hz⟩
  have hzconv := p.rootSet_derivative_subset_convexHull_rootSet
    (Polynomial.natDegree_pos_iff_degree_pos.mp (by omega)) hzset
  by_contra h
  push Not at h
  have hlin : IsLinearMap ℝ (fun w : ℂ => (w * starRingEnd ℂ z).re) := by
    constructor
    · intro a b; simp [add_mul]
    · intro a b
      change ((a : ℂ) * b * starRingEnd ℂ z).re = a * (b * starRingEnd ℂ z).re
      rw [mul_assoc, Complex.mul_re]
      simp
  have hsubset : p.rootSet ℂ ⊆ {w | (w * starRingEnd ℂ z).re < ‖z‖ ^ 2} := by
    intro w hw
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hw
    exact h w hw.2
  have hbad := (convexHull_min hsubset (convex_halfSpace_lt hlin (‖z‖ ^ 2))) hzconv
  have heq : (z * starRingEnd ℂ z).re = ‖z‖ ^ 2 := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im, Complex.sq_norm,
      Complex.normSq_apply]
    ring
  change (z * starRingEnd ℂ z).re < ‖z‖ ^ 2 at hbad
  rw [heq] at hbad
  exact (lt_irrefl _) hbad



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

namespace DerivativeChainPrivate







theorem chainCost_eq_sum_range {n : ℕ} (f : ℕ → ℂ) :
    chainCost (fun i : Fin n => f i.val) =
      ∑ i ∈ Finset.range (n - 1), ‖f (i + 1) - f i‖ := by
  unfold chainCost
  exact Fin.sum_univ_eq_sum_range (fun i => ‖f (i + 1) - f i‖) (n - 1)





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

theorem normalized_cubic_positive_root_sector (β z : ℂ)
    (hβre : 0 ≤ β.re) (hβim : 0 ≤ β.im)
    (hz : z ^ 3 - z = β) (hzre : 0 < z.re) :
    1 ≤ z.re ∧ 0 ≤ z.im ∧ 1 + 3 * z.im ^ 2 ≤ z.re ^ 2 := by
  have hre := congrArg Complex.re hz
  have him := congrArg Complex.im hz
  simp only [pow_succ, pow_zero, Complex.mul_re, Complex.mul_im,
    Complex.sub_re, Complex.sub_im, Complex.one_re, Complex.one_im] at hre him
  have hprod : 0 ≤ z.re * (z.re ^ 2 - 3 * z.im ^ 2 - 1) := by
    nlinarith only [hre, hβre]
  have hsector : 1 + 3 * z.im ^ 2 ≤ z.re ^ 2 := by
    have h := nonneg_of_mul_nonneg_right hprod hzre
    linarith
  have hcoeff : 0 < 3 * z.re ^ 2 - z.im ^ 2 - 1 := by
    nlinarith only [hsector, sq_nonneg z.im]
  have himprod : 0 ≤ z.im * (3 * z.re ^ 2 - z.im ^ 2 - 1) := by
    nlinarith only [him, hβim]
  exact ⟨by nlinarith only [hsector, sq_nonneg z.im, hzre],
    nonneg_of_mul_nonneg_left himprod hcoeff, hsector⟩

theorem normalized_cubic_positive_root_unique (β z w : ℂ)
    (hβre : 0 ≤ β.re) (hβim : 0 ≤ β.im)
    (hz : z ^ 3 - z = β) (hw : w ^ 3 - w = β)
    (hzre : 0 < z.re) (hwre : 0 < w.re) : z = w := by
  obtain ⟨hz1, _, hzs⟩ := normalized_cubic_positive_root_sector β z hβre hβim hz hzre
  obtain ⟨hw1, _, hws⟩ := normalized_cubic_positive_root_sector β w hβre hβim hw hwre
  by_contra hne
  have hmul : (z - w) * (z ^ 2 + z * w + w ^ 2 - 1) = 0 := by
    calc
      _ = (z ^ 3 - z) - (w ^ 3 - w) := by ring
      _ = 0 := by rw [hz, hw]; ring
  have hfactor := (mul_eq_zero.mp hmul).resolve_left (sub_ne_zero.mpr hne)
  have hre := congrArg Complex.re hfactor
  simp only [Complex.sub_re, Complex.add_re, Complex.mul_re, Complex.one_re,
    Complex.zero_re, pow_two] at hre
  have hprod : 1 ≤ z.re * w.re := by nlinarith only [hz1, hw1]
  nlinarith only [hre, hzs, hws, hprod, sq_nonneg (z.im - w.im),
    sq_nonneg z.im, sq_nonneg w.im]

theorem normalized_cubic_quadrant_root (β : ℂ)
    (hβre : 0 ≤ β.re) (hβim : 0 ≤ β.im) :
    ∃! z : ℂ, z ^ 3 - z = β ∧ 0 < z.re := by
  let p : Polynomial ℂ := X ^ 3 - X - C β
  let c : ℝ := Real.sqrt 3 / 3
  have hc : 0 < c := div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
  have hc2 : c ^ 2 = 1 / 3 := by
    dsimp only [c]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hdegree : p.natDegree = 3 := by
    dsimp only [p]
    compute_degree
    norm_num
  have hcritical : p.derivative.eval (c : ℂ) = 0 := by
    simp only [p, derivative_sub, derivative_X_pow, derivative_X, derivative_C,
      eval_sub, eval_mul, eval_C, eval_pow, eval_X, eval_one, Nat.cast_ofNat,
      Nat.reduceSub, sub_zero]
    have hcomplex : (c : ℂ) ^ 2 = 1 / 3 := by
      rw [← Complex.ofReal_pow, hc2, Complex.ofReal_div]
      norm_num
    linear_combination 3 * hcomplex
  obtain ⟨z, hz, hs⟩ := derivative_supporting_parent p (by rw [hdegree]; norm_num)
    (c : ℂ) hcritical
  have hzre : 0 < z.re := by
    simp only [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hc, Complex.mul_re,
      Complex.conj_re, Complex.conj_im, Complex.ofReal_re, Complex.ofReal_im,
      neg_zero, mul_zero, sub_zero] at hs
    nlinarith only [hs, hc, hc2]
  have hzeq : z ^ 3 - z = β := by
    simpa only [p, eval_sub, eval_pow, eval_X, eval_C, sub_eq_zero] using hz
  refine ⟨z, ⟨hzeq, hzre⟩, ?_⟩
  intro w hw
  exact normalized_cubic_positive_root_unique β w z hβre hβim hw.1 hzeq hw.2 hzre

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem derivative_real_supporting_parent (p : Polynomial ℂ) (hp : 0 < p.natDegree)
    (w : ℂ) (hw : p.derivative.eval w = 0) :
    ∃ z : ℂ, p.eval z = 0 ∧ w.re ≤ z.re := by
  have hd : p.derivative ≠ 0 := by
    intro h
    have hconst := Polynomial.derivative_eq_zero.mp h
    have hzero : p.natDegree = 0 := by simpa [hconst]
    omega
  have hwset : w ∈ p.derivative.rootSet ℂ := by
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval]
    exact ⟨hd, hw⟩
  have hwconv := p.rootSet_derivative_subset_convexHull_rootSet
    (Polynomial.natDegree_pos_iff_degree_pos.mp hp) hwset
  by_contra h
  push Not at h
  have hlinear : IsLinearMap ℝ (fun z : ℂ => z.re) := by
    constructor
    · intro a b; simp
    · intro a b; simp
  have hsubset : p.rootSet ℂ ⊆ {z | z.re < w.re} := by
    intro z hz
    rw [Polynomial.mem_rootSet, Polynomial.coe_aeval_eq_eval] at hz
    exact h z hz.2
  have hbad := (convexHull_min hsubset (convex_halfSpace_lt hlinear w.re)) hwconv
  exact (lt_irrefl w.re) hbad



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem inverse_graph_southeast_impossible
    (α₀ α₁ b₀ b₁ A₀ A₁ B₀ B₁ K R I x y r v : ℝ)
    (hα₁ : 0 < α₁) (hα : α₁ < α₀)
    (hx : 0 < x) (hv : 0 < v) (hxr : x ≤ r) (hvy : v ≤ y)
    (hR : 0 ≤ R) (hI : 0 ≤ I)
    (hC₀ : (3 * A₀ - B₀) / 2 ≤ K) (hC₁ : 0 ≤ (3 * A₁ - B₁) / 2)
    (hgap : K < b₀ - b₁)
    (hR₀ : R / x = α₀ * (x ^ 2 - 3 * y ^ 2) - b₀ + A₀)
    (hI₀ : I / y = α₀ * (3 * x ^ 2 - y ^ 2) - b₀ + B₀)
    (hR₁ : R / r = α₁ * (r ^ 2 - 3 * v ^ 2) - b₁ + A₁)
    (hI₁ : I / v = α₁ * (3 * r ^ 2 - v ^ 2) - b₁ + B₁) : False := by
  have hreal := div_le_div_of_nonneg_left hR hx hxr
  have himag := div_le_div_of_nonneg_left hI hv hvy
  rw [hR₀, hR₁] at hreal
  rw [hI₀, hI₁] at himag
  have hsq : v ^ 2 ≤ y ^ 2 := by nlinarith only [hv, hvy]
  have hterm₀ := mul_nonneg (sub_pos.mpr hα).le (sq_nonneg y)
  have hterm₁ := mul_nonneg hα₁.le (sub_nonneg.mpr hsq)
  nlinarith only [hreal, himag, hterm₀, hterm₁, hC₀, hC₁, hgap]



end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate





end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem quadrant_phase_forces_nonnegative_im (β z : ℂ) (k : ℝ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hx : 0 < z.re) (hk : 0 < k)
    (hphase : (β / z).im = 2 * z.re * z.im * k) :
    0 ≤ z.im ∧ (β.im = 0 → z.im = 0) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hD : 0 < Complex.normSq z := by
    rw [← Complex.sq_norm]
    exact sq_pos_of_pos (norm_pos_iff.mpr hz)
  have hquot : (β / z).im * Complex.normSq z = β.im * z.re - β.re * z.im := by
    rw [Complex.div_im]
    field_simp
  rw [hphase] at hquot
  have hcoeff : 0 < 2 * z.re * k * Complex.normSq z + β.re := by positivity
  have hprod : (2 * z.re * k * Complex.normSq z + β.re) * z.im = β.im * z.re := by
    nlinarith only [hquot]
  refine ⟨nonneg_of_mul_nonneg_right (hprod.symm ▸ mul_nonneg hI hx.le) hcoeff, ?_⟩
  intro hzero
  rw [hzero,zero_mul] at hprod
  exact (mul_eq_zero.mp hprod).resolve_left hcoeff.ne'

theorem rational_inverse_parts (β z : ℂ) (α b d c : ℝ)
    (hz : z ≠ 0) (hpole : z ^ 2 - (c : ℂ) ≠ 0)
    (hβ : β / z = (α : ℂ) * z ^ 2 - (b : ℂ) + (d : ℂ) / (z ^ 2 - (c : ℂ))) :
    let U := z.re ^ 2 + z.im ^ 2
    let D := ‖z ^ 2 - (c : ℂ)‖ ^ 2
    β.re = z.re * (α * (z.re ^ 2 - 3 * z.im ^ 2) - b + d * (U - c) / D) ∧
      β.im = z.im * (α * (3 * z.re ^ 2 - z.im ^ 2) - b - d * (U + c) / D) ∧
      (β / z).im = 2 * z.re * z.im * (α - d / D) ∧
      D = (U - c) ^ 2 + 4 * c * z.im ^ 2 := by
  have hD : Complex.normSq (z ^ 2 - (c : ℂ)) ≠ 0 := by
    simpa only [← Complex.sq_norm, ne_eq, sq_eq_zero_iff, norm_eq_zero] using hpole
  have heq := (div_eq_iff hz).mp hβ
  dsimp only
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [heq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_two, ← Complex.sq_norm]
    field_simp [hD]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · rw [heq]
    simp only [Complex.mul_re, Complex.mul_im, Complex.add_re, Complex.add_im,
      Complex.sub_re, Complex.sub_im, Complex.div_re, Complex.div_im,
      Complex.ofReal_re, Complex.ofReal_im, pow_two, ← Complex.sq_norm]
    field_simp [hD]
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im]
    ring
  · rw [hβ]
    simp only [Complex.add_im, Complex.sub_im, Complex.mul_im, Complex.mul_re,
      Complex.div_im, Complex.ofReal_re, Complex.ofReal_im, pow_two, ← Complex.sq_norm]
    field_simp [hD]
    ring
  · rw [Complex.sq_norm]
    simp only [Complex.normSq_apply, Complex.sub_re, Complex.sub_im,
      Complex.mul_re, Complex.mul_im, Complex.ofReal_re, Complex.ofReal_im, pow_two]
    ring

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

theorem cubic_graph_coordinate_parts (β z e : ℂ) (α b : ℝ) (hz : z ≠ 0)
    (hβ : β/z = (α : ℂ)*z^2-(b : ℂ)+e/z) :
    β.re = z.re * (α*(z.re^2-3*z.im^2)-b)+e.re ∧
      β.im = z.im * (α*(3*z.re^2-z.im^2)-b)+e.im ∧
      (β/z).im = 2*α*z.re*z.im+(e/z).im := by
  have hgraph : β = (α : ℂ)*z^3-(b : ℂ)*z+e := by
    calc
      _ = ((α : ℂ)*z^2-(b : ℂ)+e/z)*z := (div_eq_iff hz).mp hβ
      _ = _ := by rw [add_mul,sub_mul,div_mul_cancel₀ _ hz]; ring
  refine ⟨?_,?_,?_⟩
  · rw [hgraph]
    simp only [pow_succ,pow_zero,Complex.add_re,Complex.sub_re,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
    ring
  · rw [hgraph]
    simp only [pow_succ,pow_zero,Complex.add_im,Complex.sub_im,Complex.mul_re,Complex.mul_im,
      Complex.ofReal_re,Complex.ofReal_im,Complex.one_re,Complex.one_im]
    ring
  · rw [hβ]
    simp only [pow_two,Complex.add_im,Complex.sub_im,Complex.mul_im,Complex.mul_re,
      Complex.ofReal_re,Complex.ofReal_im]
    ring



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



end


section
-- Source module: Rows


set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial





theorem normalized_fifth_power_expansion (β : ℂ) :
    ((X^3 - C (7) * X - 91 * C β)^5 : Polynomial ℂ) =
      C (1) * X^15 +
      C (-35) * X^13 +
      C (-455*β) * X^12 +
      C (490) * X^11 +
      C (12740*β) * X^10 +
      C (82810*β^2 - 3430) * X^9 +
      C (-133770*β) * X^8 +
      C (12005 - 1739010*β^2) * X^7 +
      C (-7535710*β^3 + 624260*β) * X^6 +
      C (12173070*β^2 - 16807) * X^5 +
      C (105499940*β^3 - 1092455*β) * X^4 +
      C (342874805*β^4 - 28403830*β^2) * X^3 +
      C (-369249790*β^3) * X^2 +
      C (-2400123635*β^4) * X^1 +
      C (-6240321451*β^5) * X^0 := by
  apply Polynomial.funext
  intro z
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat]
  ring

theorem normalized_fifth_power_actual_rows (β z : ℂ) :
    let p : Polynomial ℂ := (X^3 - C (7) * X - 91 * C β)^5
    (derivative^[5] p).eval z = 360360 * (-165620*β^3*z/11 + 38220*β^2*z^4/11 - 133770*β^2*z^2/11 + 44590*β^2/11 - 120*β*z^7 + 11760*β*z^5/11 - 27440*β*z^3/11 + 13720*β*z/11 + z^10 - 15*z^8 + 980*z^6/13 - 20580*z^4/143 + 12005*z^2/143 - 2401/429) ∧
    (derivative^[6] p).eval z = 3603600 * (-16562*β^3/11 + 15288*β^2*z^3/11 - 26754*β^2*z/11 - 84*β*z^6 + 5880*β*z^4/11 - 8232*β*z^2/11 + 1372*β/11 + z^9 - 12*z^7 + 588*z^5/13 - 8232*z^3/143 + 2401*z/143) ∧
    (derivative^[7] p).eval z = 32432400 * (5096*β^2*z^2/11 - 8918*β^2/33 - 56*β*z^5 + 7840*β*z^3/33 - 5488*β*z/33 + z^8 - 28*z^6/3 + 980*z^4/39 - 2744*z^2/143 + 2401/1287) ∧
    (derivative^[8] p).eval z = 259459200 * (1274*β^2*z/11 - 35*β*z^4 + 980*β*z^2/11 - 686*β/33 + z^7 - 7*z^5 + 490*z^3/39 - 686*z/143) ∧
    (derivative^[9] p).eval z = 1816214400 * (182*β^2/11 - 20*β*z^3 + 280*β*z/11 + z^6 - 5*z^4 + 70*z^2/13 - 98/143) ∧
    (derivative^[10] p).eval z = 10897286400 * (-10*β*z^2 + 140*β/33 + z^5 - 10*z^3/3 + 70*z/39) ∧
    (derivative^[11] p).eval z = 54486432000 * (-4*β*z + z^4 - 2*z^2 + 14/39) ∧
    (derivative^[12] p).eval z = 217945728000 * (-β + z^3 - z) ∧
    (derivative^[13] p).eval z = 653837184000 * (z^2 - 1/3) ∧
    (derivative^[14] p).eval z = 1307674368000 * (z) := by
  let p : Polynomial ℂ := (X^3 - C (7) * X - 91 * C β)^5
  have hexpand := normalized_fifth_power_expansion β
  change p = _ at hexpand
  dsimp only
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  all_goals change (derivative^[_] p).eval z = _
  all_goals rw [hexpand]
  all_goals simp only [iterate_map_add, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  all_goals norm_num [Nat.descFactorial] <;> ring

end DerivativeChainPrivate

end


section
-- Source module: QuarticStep


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_quartic_step (c : ℝ) (hc : 0 ≤ c) (hcUpper : c ≤ 8/21) (β w : ℂ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hw : w ^ 3 - w = β) (hwpos : 0 < w.re) :
    ∃ z : ℂ,
      z ^ 4 - 2 * z ^ 2 - 4 * β * z + c = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 7 / 4 ≤ z.re ^ 2 ∧
      β / z = (1/4 : ℂ) * z ^ 2 - 1/2 + (c/4 : ℂ) / z ^ 2 := by
  obtain ⟨hw1,hwim,hwsector⟩ := normalized_cubic_positive_root_sector β w hR hI hw hwpos
  have hwne : w ≠ 0 := by intro h; simp [h] at hwpos
  have hwinv : β / w = (1 : ℂ) * w ^ 2 - 1 + 0 / (w ^ 2 - 0) := by
    rw [← hw]
    field_simp
    ring
  obtain ⟨hwR,hwI,hwphase,_⟩ := rational_inverse_parts β w 1 1 0 0 hwne
    (by simpa using pow_ne_zero 2 hwne) hwinv
  simp only [zero_mul,zero_div,sub_zero,add_zero,one_mul] at hwR hwI hwphase
  have hwzero := (quadrant_phase_forces_nonnegative_im β w 1 hR hI hwpos
    (by norm_num) (by simpa only [mul_one] using hwphase)).2
  let p : Polynomial ℂ := X ^ 4 - 2 * X ^ 2 - 4 * C β * X + C (c : ℂ)
  have hpdeg : p.natDegree = 4 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w = 0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 4 * hw
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx1 : 1 ≤ z.re := hw1.trans hxz
  have hx : 0 < z.re := by linarith
  have hz0 : z ≠ 0 := by intro h; simp [h] at hx
  have hzroot : z ^ 4 - 2 * z ^ 2 - 4 * β * z + c = 0 := by
    simpa only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] using hz
  have hzinv : β / z = (1 / 4 : ℂ) * z ^ 2 - 1 / 2 + (c/4 : ℂ) / (z ^ 2 - 0) := by
    have hform : β / z = (z ^ 4 - 2 * z ^ 2 + c) / (4 * z ^ 2) := by
      apply (div_eq_div_iff hz0 (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz0))).2
      linear_combination (-z) * hzroot
    rw [hform]
    field_simp
    ring
  obtain ⟨hzR,hzI,hzphase,hD⟩ := rational_inverse_parts β z (1/4) (1/2) (c/4) 0 hz0
    (by simpa using pow_ne_zero 2 hz0) (by push_cast; exact hzinv)
  simp only [Complex.ofReal_zero,sub_zero,zero_mul,mul_zero,add_zero] at hzR hzI hzphase hD
  let U := z.re ^ 2 + z.im ^ 2
  have hU : 1 ≤ U := by dsimp only [U]; nlinarith only [hx1,sq_nonneg z.im]
  have hUpos : 0 < U := by linarith
  have hDpos : 0 < ‖z ^ 2‖ ^ 2 := by rw [hD]; change 0 < U ^ 2; positivity
  have hD1 : 1 ≤ ‖z ^ 2‖ ^ 2 := by rw [hD]; change 1 ≤ U ^ 2; nlinarith only [hU]
  have hphasepos : 0 < (1/4 : ℝ) - (c/4) / ‖z ^ 2‖ ^ 2 := by
    have hquot : (c/4 : ℝ) / ‖z ^ 2‖ ^ 2 ≤ c/4 :=
      by simpa using div_le_div_of_nonneg_left (show (0 : ℝ) ≤ c/4 by positivity) (by norm_num : (0 : ℝ) < 1) hD1
    linarith
  obtain ⟨hzim,_⟩ := quadrant_phase_forces_nonnegative_im β z _ hR hI hx hphasepos hzphase
  have himorder : w.im ≤ z.im := by
    by_contra hfail
    have hlt : z.im < w.im := lt_of_not_ge hfail
    by_cases hzero : z.im = 0
    · have hβzero : β.im = 0 := by rw [hzI,hzero,zero_mul]
      have hwzero' := hwzero hβzero
      linarith
    · have hv : 0 < z.im := lt_of_le_of_ne hzim (Ne.symm hzero)
      have hy : 0 < w.im := lt_trans hv hlt
      apply inverse_graph_southeast_impossible 1 (1/4) 1 (1/2) 0
        ((c/4) * U / ‖z ^ 2‖ ^ 2) 0 (-((c/4) * U / ‖z ^ 2‖ ^ 2)) 0
        β.re β.im w.re w.im z.re z.im
        (by norm_num) (by norm_num) hwpos hv hxz hlt.le hR hI
        (by norm_num) (by
          have hA : 0 ≤ (c/4 : ℝ) * U / ‖z ^ 2‖ ^ 2 := by positivity
          linarith only [hA]) (by norm_num)
      · rw [hwR]; field_simp <;> ring
      · rw [hwI]; field_simp <;> ring
      · rw [hzR]; dsimp only [U]; field_simp <;> ring
      · rw [hzI]; dsimp only [U]; field_simp <;> ring
  have hXpos : 0 < z.re ^ 2 := sq_pos_of_pos hx
  have hbr : 0 ≤ (1/4 : ℝ) * (z.re ^ 2 - 3 * z.im ^ 2) - 1/2 +
      (c/4) * U / ‖z ^ 2‖ ^ 2 := by
    apply nonneg_of_mul_nonneg_right ?_ hx
    simpa only [U] using (hzR ▸ hR)
  have hrewrite : (c/4 : ℝ) * U / ‖z ^ 2‖ ^ 2 = (c/4) / U := by
    rw [hD]; change (c/4 : ℝ) * U / U ^ 2 = (c/4) / U
    field_simp
  rw [hrewrite] at hbr
  have hquot := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ c/4 by positivity) hXpos
    (show z.re ^ 2 ≤ U by dsimp only [U]; nlinarith only [sq_nonneg z.im])
  have hweak : 0 ≤ z.re ^ 2 / 4 - 1/2 + (c/4) / z.re ^ 2 := by
    nlinarith only [hbr,hquot,sq_nonneg z.im]
  have hid : z.re ^ 2 / 4 - 1/2 + (c/4) / z.re ^ 2 =
      ((z.re ^ 2) ^ 2 - 2 * z.re ^ 2 + c) / (4 * z.re ^ 2) := by field_simp; ring
  rw [hid] at hweak
  have hpoly := (le_div_iff₀ (show 0 < 4 * z.re ^ 2 by positivity)).mp hweak
  have hX1 : 1 ≤ z.re ^ 2 := by nlinarith only [hx1]
  have hX : 7/4 ≤ z.re ^ 2 := by
    by_contra hfail
    have hprod := mul_nonneg (show 0 ≤ z.re ^ 2 - 1 by linarith)
      (show 0 ≤ 7/4 - z.re ^ 2 by linarith)
    nlinarith only [hpoly,hprod,lt_of_not_ge hfail,hcUpper]
  exact ⟨z,hzroot,hxz,himorder,hX,by simpa only [sub_zero] using hzinv⟩

end DerivativeChainPrivate

end


section
-- Source module: QuinticStep


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_quintic_step (c d b e : ℝ)
    (hc : 0 ≤ c) (hcUpper : c ≤ 8/21) (hd : 0 ≤ d) (hdUpper : d ≤ 8/15)
    (hbUpper : b ≤ 3/10) (he : 0 ≤ e) (heUpper : e < 1/10)
    (hsum : 10*b+d = 10/3) (hcoeff : 10*(e+b*d) = 5*c) (β w : ℂ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hwpos : 0 < w.re) (hwim : 0 ≤ w.im)
    (hwX : 7/4 ≤ w.re ^ 2)
    (hwroot : w ^ 4 - 2 * w ^ 2 - 4 * β * w + c = 0)
    (hwinv : β / w = (1/4 : ℂ) * w ^ 2 - 1/2 + ((c/4) : ℂ) / w ^ 2) :
    ∃ z : ℂ,
      z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + (5*c) * z + (10*d) * β = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 5/2 ≤ z.re ^ 2 ∧
      β / z = (1/10 : ℂ) * z ^ 2 - b + (e : ℂ) / (z ^ 2 - d) := by
  have hsumC : 10*(b : ℂ)+(d : ℂ) = 10/3 := by
    have h := congrArg Complex.ofReal hsum
    push_cast at h
    exact h
  have hcoeffC : 10*((e : ℂ)+(b : ℂ)*(d : ℂ)) = 5*(c : ℂ) := by exact_mod_cast hcoeff
  have hwne : w ≠ 0 := by intro h; simp [h] at hwpos
  obtain ⟨hwR,hwI,hwphase,hwD⟩ := rational_inverse_parts β w (1/4) (1/2) ((c/4)) 0 hwne
    (by simpa using pow_ne_zero 2 hwne) (by push_cast; simpa using hwinv)
  simp only [Complex.ofReal_zero,sub_zero,zero_mul,mul_zero,add_zero] at hwR hwI hwphase hwD
  let W := w.re ^ 2 + w.im ^ 2
  have hW : 1 ≤ W := by dsimp only [W]; nlinarith only [hwX,sq_nonneg w.im]
  have hWpos : 0 < W := by linarith
  have hwD1 : 1 ≤ ‖w ^ 2‖ ^ 2 := by rw [hwD]; change 1 ≤ W ^ 2; nlinarith only [hW]
  have hwDp : 0 < ‖w ^ 2‖ ^ 2 := by linarith
  have hwphasep : 0 < (1/4 : ℝ) - ((c/4)) / ‖w ^ 2‖ ^ 2 := by
    have hquot : ((c/4) : ℝ) / ‖w ^ 2‖ ^ 2 ≤ (c/4) :=
      by simpa using div_le_div_of_nonneg_left (show (0 : ℝ) ≤ c/4 by positivity) (by norm_num : (0 : ℝ) < 1) hwD1
    linarith
  have hwzero := (quadrant_phase_forces_nonnegative_im β w _ hR hI hwpos hwphasep hwphase).2
  let p : Polynomial ℂ := X ^ 5 - C (10/3) * X ^ 3 - 10 * C β * X ^ 2 +
    C ((5*c : ℝ) : ℂ) * X + C ((10*d : ℝ) : ℂ) * C β
  have hpdeg : p.natDegree = 5 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w = 0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 5 * hwroot
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hXpre : 7/4 ≤ z.re ^ 2 := by nlinarith only [hwX,hxz,hwpos]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hx
  have hpole : z ^ 2 - (d : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
    have hm : z.re * z.im = 0 := by nlinarith only [hi]
    have hy := (mul_eq_zero.mp hm).resolve_left hx.ne'
    rw [hy] at hr
    nlinarith only [hr,hXpre,hdUpper]
  have hzroot : z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + (5*c) * z + (10*d) * β = 0 := by
    have ht := hz
    simp only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] at ht
    push_cast at ht
    exact ht
  have hzinv : β / z = (1/10 : ℂ) * z ^ 2 - b + (e : ℂ) / (z ^ 2 - d) := by
    have hform : β / z = (z ^ 4 - 10/3 * z ^ 2 + (5*c)) / (10 * (z ^ 2 - d)) := by
      apply (div_eq_div_iff hz0 (mul_ne_zero (by norm_num) hpole)).2
      linear_combination -hzroot
    rw [hform]
    apply (div_eq_iff (mul_ne_zero (by norm_num : (10 : ℂ) ≠ 0) hpole)).2
    calc
      _ = ((1/10 : ℂ) * z ^ 2 - b) * (10 * (z ^ 2 - d)) + (e) * 10 := by
        linear_combination z^2 * hsumC - hcoeffC
      _ = ((1/10 : ℂ) * z ^ 2 - b) * (10 * (z ^ 2 - d)) +
          ((e) / (z ^ 2 - d) * (z ^ 2 - d)) * 10 := by rw [div_mul_cancel₀ _ hpole]
      _ = _ := by ring
  obtain ⟨hzR,hzI,hzphase,hD⟩ := rational_inverse_parts β z (1/10) (b) (e) (d)
    hz0 (by push_cast; exact hpole) (by push_cast; exact hzinv)
  push_cast at hzR hzI hzphase hD
  let U := z.re ^ 2 + z.im ^ 2
  let D := ‖z ^ 2 - (d : ℂ)‖ ^ 2
  have hU : 7/4 ≤ U := by dsimp only [U]; nlinarith only [hXpre,sq_nonneg z.im]
  have hUc : 1 ≤ U - d := by linarith
  have hUcp : 0 < U - d := by linarith
  have hDlow : (U - d) ^ 2 ≤ D := by
    dsimp only [U,D]
    nlinarith only [hD,mul_nonneg hd (sq_nonneg z.im)]
  have hD1 : 1 ≤ D := by nlinarith only [hDlow,hUc]
  have hDp : 0 < D := by linarith
  have hphasep : 0 < (1/10 : ℝ) - (e) / D := by
    have hquot : (e : ℝ) / D ≤ e := by simpa using div_le_div_of_nonneg_left he (by norm_num : (0 : ℝ) < 1) hD1
    linarith
  obtain ⟨hzim,_⟩ := quadrant_phase_forces_nonnegative_im β z _ hR hI hx hphasep hzphase
  have himorder : w.im ≤ z.im := by
    by_contra hfail
    have hlt : z.im < w.im := lt_of_not_ge hfail
    by_cases hzero : z.im = 0
    · have hβzero : β.im = 0 := by rw [hzI,hzero,zero_mul]
      have hwzero' := hwzero hβzero
      linarith
    · have hv : 0 < z.im := lt_of_le_of_ne hzim (Ne.symm hzero)
      have hy : 0 < w.im := lt_trans hv hlt
      have hCw : (3 * (((c/4)) * W / ‖w ^ 2‖ ^ 2) - (-(((c/4)) * W / ‖w ^ 2‖ ^ 2))) / 2 ≤ 4/21 := by
        have hid : (3 * (((c/4)) * W / ‖w ^ 2‖ ^ 2) - (-(((c/4)) * W / ‖w ^ 2‖ ^ 2))) / 2 =
            (c/2 : ℝ) / W := by rw [hwD]; change _ = (c/2 : ℝ) / W; field_simp; ring
        rw [hid]
        apply (div_le_iff₀ hWpos).2
        linarith
      have hAz : 0 ≤ (e : ℝ) * (U - d) / D := by positivity
      have hBz : 0 ≤ (e : ℝ) * (U + d) / D := by positivity
      apply inverse_graph_southeast_impossible (1/4) (1/10) (1/2) (b)
        (((c/4)) * W / ‖w ^ 2‖ ^ 2) ((e) * (U-d) / D)
        (-(((c/4)) * W / ‖w ^ 2‖ ^ 2)) (-((e) * (U+d) / D)) (4/21)
        β.re β.im w.re w.im z.re z.im
        (by norm_num) (by norm_num) hwpos hv hxz hlt.le hR hI hCw
        (by linarith only [hAz,hBz]) (by linarith only [hbUpper])
      · rw [hwR]; dsimp only [W]; field_simp <;> ring
      · rw [hwI]; dsimp only [W]; field_simp <;> ring
      · rw [hzR]; dsimp only [U,D]; field_simp <;> ring
      · rw [hzI]; dsimp only [U,D]; field_simp <;> ring
  have hXcp : 0 < z.re ^ 2 - d := by linarith
  have hA : (e : ℝ) * (U - d) / D ≤ (e) / (z.re ^ 2 - d) := by
    calc
      _ ≤ (e) / (U-d) := by
        apply (div_le_div_iff₀ hDp hUcp).2
        nlinarith only [mul_le_mul_of_nonneg_left hDlow (show (0 : ℝ) ≤ e from he)]
      _ ≤ _ := div_le_div_of_nonneg_left he hXcp
        (by dsimp only [U]; nlinarith only [sq_nonneg z.im])
  have hbr : 0 ≤ (1/10 : ℝ) * (z.re ^ 2 - 3 * z.im ^ 2) - b + (e) * (U-d) / D := by
    apply nonneg_of_mul_nonneg_right ?_ hx
    simpa only [U,D] using (hzR ▸ hR)
  have hweak : 0 ≤ z.re ^ 2 - (10*b) + ((10*e)) / (z.re ^ 2 - d) := by
    have hcoeff : ((10*e) : ℝ) / (z.re ^ 2 - d) =
        10 * ((e) / (z.re ^ 2 - d)) := by ring
    rw [hcoeff]
    nlinarith only [hbr,hA,sq_nonneg z.im]
  have hid : z.re ^ 2 - (10*b) + ((10*e)) / (z.re ^ 2 - d) =
      ((z.re ^ 2) ^ 2 - 10/3 * z.re ^ 2 + (5*c)) / (z.re ^ 2 - d) := by
    apply (eq_div_iff hXcp.ne').2
    calc
      _ = (z.re ^ 2 - (10*b)) * (z.re ^ 2 - d) +
          (((10*e)) / (z.re ^ 2 - d)) * (z.re ^ 2 - d) := by ring
      _ = (z.re ^ 2 - (10*b)) * (z.re ^ 2 - d) + (10*e) := by rw [div_mul_cancel₀ _ hXcp.ne']
      _ = _ := by linear_combination -(z.re^2)*hsum + hcoeff
  rw [hid] at hweak
  have hpoly := (le_div_iff₀ hXcp).mp hweak
  have hX : 5/2 ≤ z.re ^ 2 := by
    by_contra hfail
    have hprod := mul_nonneg (show 0 ≤ z.re ^ 2 - 7/4 by linarith)
      (show 0 ≤ 5/2 - z.re ^ 2 by linarith)
    nlinarith only [hpoly,hprod,lt_of_not_ge hfail,hcUpper]
  exact ⟨z,hzroot,hxz,himorder,hX,hzinv⟩

end DerivativeChainPrivate

end


section
-- Source module: PrefixFive


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



theorem normalized_fifth_prefix_five (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin 5 → ℂ,
      (∀ i, (derivative^[15-(i.val+1)] ((X^3-C (7)*X-91*C β)^5)).eval (z i) = 0) ∧
      z 0 = 0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0 < (z 4).re ∧ 5/2 ≤ (z 4).re^2 ∧
      β / z 4 = (1/10 : ℂ)*(z 4)^2-(16/55)+(441/7865)/((z 4)^2-(14/33)) := by
  obtain ⟨w₃,hw₃,_⟩ := normalized_cubic_quadrant_root β hR hI
  obtain ⟨hw₃re,hw₃im,_⟩ := normalized_cubic_positive_root_sector β w₃ hR hI hw₃.1 hw₃.2
  obtain ⟨w₄,hw₄,h₃₄r,h₃₄i,hw₄X,hw₄inv⟩ :=
    normalized_quartic_step (14/39) (by norm_num) (by norm_num) β w₃ hR hI hw₃.1 hw₃.2
  have hw₄pos : 0 < w₄.re := lt_of_lt_of_le hw₃.2 h₃₄r
  obtain ⟨w₅,hw₅,h₄₅r,h₄₅i,hw₅X,hw₅inv⟩ :=
    normalized_quintic_step (14/39) (14/33) (16/55) (441/7865)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      β w₄ hR hI hw₄pos (hw₃im.trans h₃₄i) hw₄X hw₄ hw₄inv
  norm_num at hw₄ hw₄inv hw₅ hw₅inv
  have hw₅pos : 0 < w₅.re := lt_of_lt_of_le hw₄pos h₄₅r
  let r : ℝ := Real.sqrt 3 / 3
  have hrpos : 0 < r := div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
  have hr2 : r^2 = 1/3 := by
    dsimp only [r]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hr1 : r ≤ 1 := by nlinarith only [hr2,hrpos]
  have hrc : (r : ℂ)^2 = 1/3 := by
    rw [←Complex.ofReal_pow,hr2,Complex.ofReal_div]
    norm_num
  let g : ℕ → ℂ
    | 0 => 0
    | 1 => (r : ℂ)
    | 2 => w₃
    | 3 => w₄
    | _ => w₅
  have hre : ∀ i < 4, (g i).re ≤ (g (i+1)).re := by
    intro i hi
    interval_cases i <;> norm_num [g] <;> linarith only [hrpos,hr1,hw₃re,h₃₄r,h₄₅r]
  have him : ∀ i < 4, (g i).im ≤ (g (i+1)).im := by
    intro i hi
    interval_cases i <;> norm_num [g] <;> linarith only [hw₃im,h₃₄i,h₄₅i]
  have hrows (i : ℕ) (hi : i < 5) :
      (derivative^[15-(i+1)] ((X^3-C (7)*X-91*C β)^5)).eval (g i) = 0 := by
    interval_cases i
    · rw [(normalized_fifth_power_actual_rows β (g 0)).2.2.2.2.2.2.2.2.2]
      simp only [g,mul_zero]
    · rw [(normalized_fifth_power_actual_rows β (g 1)).2.2.2.2.2.2.2.2.1]
      simp only [g,hrc]
      norm_num
    · rw [(normalized_fifth_power_actual_rows β (g 2)).2.2.2.2.2.2.2.1]
      simp only [g]
      linear_combination 217945728000 * hw₃.1
    · rw [(normalized_fifth_power_actual_rows β (g 3)).2.2.2.2.2.2.1]
      simp only [g]
      linear_combination 54486432000 * hw₄
    · rw [(normalized_fifth_power_actual_rows β (g 4)).2.2.2.2.2.1]
      simp only [g]
      linear_combination 10897286400 * hw₅
  refine ⟨fun i => g i.val,fun i => hrows i.val i.isLt,rfl,?_,?_,hw₅pos,hw₅X,hw₅inv⟩
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt

end DerivativeChainPrivate

end


section
-- Source module: SexticPick


set_option autoImplicit false
open Set
namespace DerivativeChainPrivate







theorem sexticUpperBranch_sq (a b c : ℝ) (z : ℂ) :
    (sexticUpperBranch a b c z)^2 = sexticRadicand a b c z := by
  rw [sexticUpperBranch,mul_pow]
  have hs : (Complex.sqrt (-sexticRadicand a b c z))^2 = -sexticRadicand a b c z :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2 : ℕ) ≠ 0)
  rw [hs,Complex.I_sq]
  ring

theorem sexticUpperBranch_im_pos (a b c : ℝ) (z : ℂ)
    (havoid : (sexticRadicand a b c z).im ≠ 0 ∨ (sexticRadicand a b c z).re < 0) :
    0 < (sexticUpperBranch a b c z).im := by
  simp only [sexticUpperBranch,Complex.mul_im,Complex.I_re,Complex.I_im,
    one_mul,zero_mul,zero_add]
  rw [Complex.sqrt,Complex.cpow_inv_two_re]
  apply Real.sqrt_pos.mpr
  rcases havoid with hi | hr
  · have hn := Complex.abs_re_lt_norm.mpr (show (-sexticRadicand a b c z).im ≠ 0 by simpa using hi)
    have ha := neg_abs_le (-sexticRadicand a b c z).re
    linarith
  · simp only [Complex.neg_re]
    have hn := norm_nonneg (-sexticRadicand a b c z)
    linarith







end DerivativeChainPrivate

end


section
-- Source module: SexticBoundary


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sexticRadicand_im_identity (a b c : ℝ) (z : ℂ) (hz : z ≠ 0) :
    (sexticRadicand a b c z).im*(z.re^2+z.im^2) =
      z.im*((2*z.re+a)*(z.re^2+z.im^2)-c) := by
  have hd : z.re^2+z.im^2 ≠ 0 := by
    simpa [Complex.normSq_apply,pow_two] using ne_of_gt (Complex.normSq_pos.mpr hz)
  simp only [sexticRadicand,pow_two,Complex.add_im,Complex.mul_im,
    Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,Complex.div_im]
  simp only [Complex.normSq_apply]
  field_simp
  ring

theorem sexticRadicand_real (a b c x : ℝ) :
    sexticRadicand a b c (x : ℂ) = ((x^2+a*x+b+c/x : ℝ) : ℂ) := by
  simp [sexticRadicand]



theorem fifth_sextic_real_exterior (x : ℝ) (hx : x ≤ -1/4 ∨ 3/2 ≤ x) :
    0 < x^2+(-35/17)*x+490/561+(686/5049)/x := by
  rcases hx with hl | hr
  · have hx0 : x < 0 := by linarith
    have h3 : 0 ≤ (-1/4-x)^3 := pow_nonneg (by linarith) 3
    have h2 := sq_nonneg (x+1/4)
    have he : (x^2+(-35/17)*x+490/561+(686/5049)/x)*x =
      x^3+(-35/17)*x^2+(490/561)*x+686/5049 := by field_simp [ne_of_lt hx0] <;> ring
    nlinarith
  · have hx0 : 0 < x := by linarith
    have h3 : 0 ≤ (x-3/2)^3 := pow_nonneg (by linarith) 3
    have h2 := sq_nonneg (x-3/2)
    have he : (x^2+(-35/17)*x+490/561+(686/5049)/x)*x =
      x^3+(-35/17)*x^2+(490/561)*x+686/5049 := by field_simp [ne_of_gt hx0] <;> ring
    nlinarith

theorem sexticRadicand_slit_exterior (a b c : ℝ)
    (ha : -11/5 ≤ a) (ha0 : a < 0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hreal : ∀ x : ℝ, x ≤ -1/4 ∨ 3/2 ≤ x → 0 < x^2+a*x+b+c/x)
    (z : ℂ) (hz : z.re ≤ -1/4 ∨ 3/2 ≤ z.re) :
    sexticRadicand a b c z ∈ Complex.slitPlane := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hz; rcases hz with h|h <;> norm_num at h
  rw [Complex.mem_slitPlane_iff]
  by_cases hi : z.im = 0
  · left
    have he : z = (z.re : ℂ) := by apply Complex.ext <;> simp [hi]
    rw [he,sexticRadicand_real,Complex.ofReal_re]
    exact hreal _ hz
  · right
    have hid := sexticRadicand_im_identity a b c z hz0
    intro hzero
    rw [hzero,zero_mul] at hid
    have hfactor : (2*z.re+a)*(z.re^2+z.im^2)-c=0 :=
      (mul_eq_zero.mp hid.symm).resolve_left hi
    have hd : 0 < z.re^2+z.im^2 := by positivity
    rcases hz with hl|hr
    · have hf : 2*z.re+a < 0 := by linarith
      have hp := mul_neg_of_neg_of_pos hf hd
      linarith
    · have hf : 4/5 ≤ 2*z.re+a := by linarith
      have hd' : 9/4 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
      have hp := mul_le_mul hf hd' (by norm_num : (0:ℝ) ≤ 9/4) (by linarith : 0 ≤ 2*z.re+a)
      nlinarith

end DerivativeChainPrivate

end


section
-- Source module: SexticExtension


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sqrt_im_sign (w : ℂ) (hw : w.im ≠ 0) :
    0 < (Complex.sqrt w).re ∧ (Complex.sqrt w).im * w.im > 0 := by
  have hs : (Complex.sqrt w)^2 = w := Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  have hr : 0 < (Complex.sqrt w).re := by
    rw [Complex.sqrt,Complex.cpow_inv_two_re]
    apply Real.sqrt_pos.mpr
    have hn := Complex.abs_re_lt_norm.mpr hw
    have ha := neg_abs_le w.re
    linarith
  have hi := congrArg Complex.im hs
  simp only [pow_two,Complex.mul_im] at hi
  have hsi : (Complex.sqrt w).im ≠ 0 := by intro he; simp [he] at hi; exact hw hi.symm
  have hp := mul_pos hr (sq_pos_of_ne_zero hsi)
  constructor
  · exact hr
  · have he := congrArg (fun x : ℝ => (Complex.sqrt w).im*x) hi
    nlinarith only [he,hp]

theorem sexticUpperBranch_eq_sqrt_of_im_pos (a b c : ℝ) (z : ℂ)
    (hi : 0 < (sexticRadicand a b c z).im) :
    sexticUpperBranch a b c z = Complex.sqrt (sexticRadicand a b c z) := by
  have hF := sexticUpperBranch_im_pos a b c z (Or.inl (ne_of_gt hi))
  have hS := (sqrt_im_sign _ (ne_of_gt hi)).2
  have hSpos : 0 < (Complex.sqrt (sexticRadicand a b c z)).im := by nlinarith
  have hs : (Complex.sqrt (sexticRadicand a b c z))^2 = sexticRadicand a b c z :=
    Complex.cpow_nat_inv_pow _ (by norm_num : (2:ℕ) ≠ 0)
  rcases (sq_eq_sq_iff_eq_or_eq_neg).mp ((sexticUpperBranch_sq a b c z).trans hs.symm) with h|h
  · exact h
  · have hh := congrArg Complex.im h
    simp only [Complex.neg_im] at hh
    linarith



theorem sexticRadicand_im_right (a b c : ℝ) (ha : -11/5 ≤ a) (hc : c ≤ 1)
    (z : ℂ) (hx : 3/2 ≤ z.re) (hy : 0 < z.im) :
    0 < (sexticRadicand a b c z).im := by
  have hz0 : z ≠ 0 := by intro he; simp [he] at hy
  have hd : 0 < z.re^2+z.im^2 := by positivity
  have hf : 4/5 ≤ 2*z.re+a := by linarith
  have hd' : 9/4 ≤ z.re^2+z.im^2 := by nlinarith [sq_nonneg z.im]
  have hp := mul_le_mul hf hd' (by norm_num : (0:ℝ) ≤ 9/4) (by linarith : 0 ≤ 2*z.re+a)
  have hfpos : 0 < (2*z.re+a)*(z.re^2+z.im^2)-c := by nlinarith
  have hi := sexticRadicand_im_identity a b c z hz0
  have hm := mul_pos hy hfpos
  nlinarith



end DerivativeChainPrivate

end


section
-- Source module: SexticSupport


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set



theorem sexticExteriorExtension_continuous (a b c σ : ℝ) (f : ℝ → ℝ)
    (hf : Continuous f)
    (hf0 : ∀ x, f x ≠ 0)
    (hslit : ∀ z : ℂ, sexticRadicand a b c ((f z.re:ℂ)+Complex.I*(z.im:ℂ)) ∈ Complex.slitPlane) :
    Continuous (sexticExteriorExtension a b c σ f) := by
  have hw : Continuous (fun z : ℂ => ((f z.re:ℂ)+Complex.I*(z.im:ℂ))) := by fun_prop
  have hw0 : ∀ z : ℂ, ((f z.re:ℂ)+Complex.I*(z.im:ℂ)) ≠ 0 := by
    intro z h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.ofReal_re,Complex.mul_re,Complex.I_re,
      Complex.I_im,Complex.ofReal_im,zero_mul,mul_zero,sub_self,add_zero,Complex.zero_re] at hr
    exact hf0 _ hr
  have hH : Continuous (fun z : ℂ => sexticRadicand a b c ((f z.re:ℂ)+Complex.I*(z.im:ℂ))) := by
    unfold sexticRadicand
    fun_prop
  have hs : Continuous (fun z : ℂ => Complex.sqrt (sexticRadicand a b c ((f z.re:ℂ)+Complex.I*(z.im:ℂ)))) := by
    apply continuous_iff_continuousAt.mpr
    intro z
    simpa only [Function.comp_def] using
      ContinuousAt.comp (f := fun w : ℂ => sexticRadicand a b c ((f w.re:ℂ)+Complex.I*(w.im:ℂ)))
        (Complex.differentiableAt_sqrt (hslit z)).continuousAt (hH.continuousAt (x := z))
  unfold sexticExteriorExtension
  fun_prop





end DerivativeChainPrivate

end


section
-- Source module: CauchyBoundary


set_option autoImplicit false
open MeasureTheory Filter Set
open scoped Topology
namespace DerivativeChainPrivate

theorem borelTransform_vertical_limit (μ : Measure ℝ) [IsFiniteMeasure μ]
    (B T : ℝ) (hT : B < T) (hμ : ∀ᵐ t ∂μ, t ≤ B) :
    Tendsto (fun ε : ℝ => TeschlQM.Herglotz.borelTransform μ ((T:ℂ)+(ε:ℂ)*Complex.I))
      (𝓝 0) (𝓝 (TeschlQM.Herglotz.borelTransform μ (T:ℂ))) := by
  unfold TeschlQM.Herglotz.borelTransform
  have hc : ContinuousAt (fun ε : ℝ => ∫ t : ℝ, ((t:ℂ)-((T:ℂ)+(ε:ℂ)*Complex.I))⁻¹ ∂μ) 0 := by
    apply continuousAt_of_dominated (bound := fun _ => (T-B)⁻¹)
    · exact Eventually.of_forall (fun ε => ((Complex.measurable_ofReal.sub_const _).inv).aestronglyMeasurable)
    · apply Eventually.of_forall
      intro ε
      filter_upwards [hμ] with t ht
      rw [norm_inv]
      apply inv_anti₀ (sub_pos.mpr hT)
      calc
        T-B ≤ T-t := by linarith
        _ ≤ |t-T| := by rw [abs_of_neg (by linarith : t-T < 0)]; ring_nf; rfl
        _ = |((t:ℂ)-((T:ℂ)+(ε:ℂ)*Complex.I)).re| := by simp
        _ ≤ ‖(t:ℂ)-((T:ℂ)+(ε:ℂ)*Complex.I)‖ := Complex.abs_re_le_norm _
    · exact integrable_const _
    · filter_upwards [hμ] with t ht
      apply ContinuousAt.inv₀ (by fun_prop)
      simp only [Complex.ofReal_zero,zero_mul,add_zero,sub_ne_zero]
      exact_mod_cast (show t ≠ T by linarith)
  simpa using hc.tendsto

theorem sextic_measure_real_value (a b c : ℝ)
    (ha : -11/5 ≤ a) (ha0 : a < 0) (hc : 0 < c) (hc1 : c ≤ 1)
    (hreal : ∀ x : ℝ, x ≤ -1/4 ∨ 3/2 ≤ x → 0 < x^2+a*x+b+c/x)
    (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ z : ℂ, 0 < z.im → sexticShift a b c z = TeschlQM.Herglotz.borelTransform μ z)
    (T : ℝ) (hT : 3/2 < T) :
    TeschlQM.Herglotz.borelTransform μ (T:ℂ) =
      ((Real.sqrt (T^2+a*T+b+c/T)-T-a/2 : ℝ):ℂ) := by
  let f : ℝ → ℝ := fun x => max (3/2) x
  let E := sexticExteriorExtension a b c 1 f
  have hf : ∀ x, 3/2 ≤ f x := fun x => le_max_left _ _
  have hf0 : ∀ x, f x ≠ 0 := by intro x; have := hf x; linarith
  have hE : Continuous E := sexticExteriorExtension_continuous a b c 1 f
    (by dsimp [f]; fun_prop) hf0 (fun z => sexticRadicand_slit_exterior a b c ha ha0 hc hc1 hreal _
      (Or.inr (by simpa using hf z.re)))
  have heq : ∀ ε : ℝ, 0 < ε → E ((T:ℂ)+(ε:ℂ)*Complex.I) =
      TeschlQM.Herglotz.borelTransform μ ((T:ℂ)+(ε:ℂ)*Complex.I) := by
    intro ε hε
    have hz : 0 < ((T:ℂ)+(ε:ℂ)*Complex.I).im := by simpa using hε
    rw [← hμ _ hz]
    dsimp only [E,sexticExteriorExtension,sexticShift]
    simp only [Complex.add_re,Complex.add_im,Complex.ofReal_re,Complex.ofReal_im,
      Complex.mul_re,Complex.mul_im,Complex.I_re,Complex.I_im,mul_zero,mul_one,
      zero_mul,zero_add,sub_zero,add_zero,Complex.ofReal_one,one_mul]
    rw [show f T = T by exact max_eq_right hT.le]
    rw [sexticUpperBranch_eq_sqrt_of_im_pos a b c _
      (sexticRadicand_im_right a b c ha hc1 _ (by simpa using hT.le) hz)]
    congr 2 <;> ring
  have hv : E (T:ℂ) = ((Real.sqrt (T^2+a*T+b+c/T)-T-a/2 : ℝ):ℂ) := by
    dsimp only [E,sexticExteriorExtension]
    simp only [Complex.ofReal_re,Complex.ofReal_im,Complex.ofReal_zero,mul_zero,add_zero,
      Complex.ofReal_one,one_mul]
    rw [show f T = T by exact max_eq_right hT.le,sexticRadicand_real]
    rw [Complex.sqrt_of_nonneg (by exact_mod_cast (hreal T (Or.inr hT.le)).le)]
    simp only [Complex.ofReal_re]
    push_cast
    rfl
  have hlim : Tendsto (fun ε : ℝ => E ((T:ℂ)+(ε:ℂ)*Complex.I)) (𝓝[>]0) (𝓝 (E (T:ℂ))) := by
    have ht : Tendsto (fun ε : ℝ => ((T:ℂ)+(ε:ℂ)*Complex.I)) (𝓝 0) (𝓝 (T:ℂ)) := by
      simpa using (show Continuous (fun ε : ℝ => ((T:ℂ)+(ε:ℂ)*Complex.I)) by fun_prop).tendsto 0
    exact (hE.continuousAt.tendsto.comp ht).mono_left nhdsWithin_le_nhds
  have hlim' := (borelTransform_vertical_limit μ (3/2) T hT (hsupp.mono fun t ht => ht.2)).mono_left
    (show 𝓝[>] (0:ℝ) ≤ 𝓝 0 from nhdsWithin_le_nhds)
  have hevent : (fun ε : ℝ => E ((T:ℂ)+(ε:ℂ)*Complex.I)) =ᶠ[𝓝[>]0]
      (fun ε : ℝ => TeschlQM.Herglotz.borelTransform μ ((T:ℂ)+(ε:ℂ)*Complex.I)) := by
    filter_upwards [self_mem_nhdsWithin] with ε hε using heq ε hε
  exact (tendsto_nhds_unique hlim' (hlim.congr' hevent)).trans hv

end DerivativeChainPrivate

namespace DerivativeChainPrivate
open MeasureTheory

theorem real_cauchy_integral_of_borel_value (μ : Measure ℝ) (T V : ℝ)
    (hV : TeschlQM.Herglotz.borelTransform μ (T:ℂ) = (V:ℂ)) :
    (∫ t : ℝ, 1/(T-t) ∂μ) = -V := by
  have hi : TeschlQM.Herglotz.borelTransform μ (T:ℂ) =
      -((∫ t : ℝ, 1/(T-t) ∂μ : ℝ):ℂ) := by
    unfold TeschlQM.Herglotz.borelTransform
    rw [← integral_complex_ofReal,← integral_neg]
    apply integral_congr_ae
    exact Filter.Eventually.of_forall (fun t => by
      push_cast
      rw [one_div,← inv_neg]
      congr 1
      ring)
  rw [hV] at hi
  have hr := congrArg Complex.re hi
  simp only [Complex.ofReal_re,Complex.neg_re] at hr
  linarith

end DerivativeChainPrivate

end


section
-- Source module: MeasureKernels


set_option autoImplicit false
namespace DerivativeChainPrivate

theorem sextic_kernel_bounds (X Y t T : ℝ) (hT : 5/2 ≤ T) (hX : T ≤ X)
    (hY : 0 ≤ Y) (htl : -1/4 ≤ t) (htu : t ≤ 3/2) :
    let D := (X-t)^2+2*(X+t)*Y+Y^2
    0 < D ∧ 0 ≤ (X+Y-t)/D ∧ 0 ≤ (X+Y+t)/D ∧
      0 ≤ (2*(X+Y)-t)/D ∧ (X+Y-t)/D ≤ 1/(T-t) := by
  have hXt : 0 < X-t := by linarith
  have hTt : 0 < T-t := by linarith
  have hXp : 0 < X+t := by linarith
  have hX3t : 0 < X+3*t := by linarith
  have hD : 0 < (X-t)^2+2*(X+t)*Y+Y^2 := by positivity
  refine ⟨hD,div_nonneg (by linarith) hD.le,div_nonneg (by linarith) hD.le,
    div_nonneg (by linarith) hD.le,?_⟩
  apply le_trans (b := 1/(X-t))
  · apply (div_le_div_iff₀ hD hXt).mpr
    have hp := mul_nonneg hX3t.le hY
    nlinarith only [hp,sq_nonneg Y]
  · exact one_div_le_one_div_of_le hTt (by linarith)




theorem sextic_kernel_inverse_bound (X Y t T : ℝ) (hT : 5/2 ≤ T) (hX : T ≤ X)
    (hY : 0 ≤ Y) (htl : -1/4 ≤ t) (htu : t ≤ 3/2) :
    1/((X-t)^2+2*(X+t)*Y+Y^2) ≤ (1/(T-t))/(T-3/2) := by
  have hXt : 0 < X-t := by linarith
  have hTt : 0 < T-t := by linarith
  have hTb : 0 < T-3/2 := by linarith
  have hXp : 0 < X+t := by linarith
  have hD : 0 < (X-t)^2+2*(X+t)*Y+Y^2 := by positivity
  rw [div_div]
  apply (div_le_div_iff₀ hD (mul_pos hTt hTb)).mpr
  have hp := mul_nonneg hXp.le hY
  have htprod := mul_nonneg (show 0 ≤ 3/2-t by linarith) hTt.le
  have hxprod := mul_nonneg (show 0 ≤ X-T by linarith) (show 0 ≤ X+T-2*t by linarith)
  nlinarith only [hp,htprod,hxprod,sq_nonneg Y]

theorem sextic_kernel_B_bound (X Y t T : ℝ) (hT : 5/2 ≤ T) (hX : T ≤ X)
    (hY : 0 ≤ Y) (htl : -1/4 ≤ t) (htu : t ≤ 3/2) :
    (X+Y+t)/((X-t)^2+2*(X+t)*Y+Y^2) ≤ (1+3/(T-3/2))*(1/(T-t)) := by
  obtain ⟨hD,_,_,_,hA⟩ := sextic_kernel_bounds X Y t T hT hX hY htl htu
  have hInv := sextic_kernel_inverse_bound X Y t T hT hX hY htl htu
  have ht : 2*t/((X-t)^2+2*(X+t)*Y+Y^2) ≤ 3/((X-t)^2+2*(X+t)*Y+Y^2) := by
    apply div_le_div_of_nonneg_right (by linarith) hD.le
  calc
    _ = (X+Y-t)/((X-t)^2+2*(X+t)*Y+Y^2)+2*t/((X-t)^2+2*(X+t)*Y+Y^2) := by ring
    _ ≤ 1/(T-t)+3*((1/(T-t))/(T-3/2)) := by
      apply add_le_add hA
      apply ht.trans
      convert mul_le_mul_of_nonneg_left hInv (by norm_num : (0:ℝ) ≤ 3) using 1 <;> ring
    _ = _ := by ring

end DerivativeChainPrivate

end


section
-- Source module: CauchyRootKernel


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem cauchy_root_kernel_bound (z : ℂ) (hx : 5/2 ≤ z.re^2) (t : ℝ)
    (ht : t ∈ Icc (-1/4:ℝ) (3/2)) :
    z^2-(t:ℂ) ≠ 0 ∧ ‖(z^2-(t:ℂ))⁻¹‖ ≤ (z.re^2-3/2)⁻¹ := by
  have htabs : |t| ≤ 3/2 := abs_le.mpr ⟨by linarith [ht.1],ht.2⟩
  have hn : z.re^2-3/2 ≤ ‖z^2-(t:ℂ)‖ := by
    have htri := norm_sub_norm_le (z^2) (t:ℂ)
    rw [norm_pow,Complex.norm_real,Real.norm_eq_abs] at htri
    have hsq : z.re^2 ≤ ‖z‖^2 := by
      rw [Complex.sq_norm,Complex.normSq_apply]
      nlinarith [sq_nonneg z.im]
    linarith
  have hp : 0 < z.re^2-3/2 := by linarith
  constructor
  · exact norm_pos_iff.mp (lt_of_lt_of_le hp hn)
  · rw [norm_inv]
    exact inv_anti₀ hp hn

theorem cauchy_kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (z : ℂ) (hx : 5/2 ≤ z.re^2) :
    Integrable (fun t : ℝ => (z^2-(t:ℂ))⁻¹) μ := by
  apply Integrable.of_bound ((measurable_const.sub Complex.measurable_ofReal).inv).aestronglyMeasurable
    (z.re^2-3/2)⁻¹
  filter_upwards [hsupp] with t ht
  exact (cauchy_root_kernel_bound z hx t ht).2

theorem cauchy_root_kernel_parts (z : ℂ) (hxpos : 0 < z.re)
    (hx : 5/2 ≤ z.re^2) (t : ℝ) (ht : t ∈ Icc (-1/4:ℝ) (3/2)) :
    let D := (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4
    (z/(z^2-(t:ℂ))).re = z.re*((z.re^2+z.im^2-t)/D) ∧
    (z/(z^2-(t:ℂ))).im = -z.im*((z.re^2+z.im^2+t)/D) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hxpos
  have hpole := (cauchy_root_kernel_bound z hx t ht).1
  obtain ⟨hr,hi,_,hd⟩ := rational_inverse_parts (z/(z^2-(t:ℂ))) z 0 0 1 t hz hpole
    (by simp; field_simp)
  simp only [Complex.ofReal_zero,Complex.ofReal_one,zero_mul,sub_zero,zero_add,one_mul,zero_sub] at hr hi
  have hd' : ‖z^2-(t:ℂ)‖^2 = (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4 := by
    rw [hd]; ring
  rw [hd'] at hr hi
  refine ⟨hr,?_⟩
  simpa only [mul_neg,neg_mul] using hi

end DerivativeChainPrivate

end


section
-- Source module: CauchyRootBounds


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem cauchy_real_kernel_integrable (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2)) (T : ℝ) (hT : 3/2 < T) :
    Integrable (fun t : ℝ => 1/(T-t)) μ := by
  have hm : Measurable (fun t : ℝ => 1/(T-t)) := measurable_const.div (measurable_const.sub measurable_id)
  apply Integrable.of_bound hm.aestronglyMeasurable (1/(T-3/2))
  filter_upwards [hsupp] with t ht
  have hp : 0 < T-t := by linarith [ht.2]
  rw [Real.norm_eq_abs,abs_of_pos (one_div_pos.mpr hp)]
  exact one_div_le_one_div_of_le (by linarith) (by linarith [ht.2])

theorem cauchy_root_corrections (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (z : ℂ) (hxpos : 0 < z.re) (hypos : 0 < z.im)
    (T : ℝ) (hT : 5/2 ≤ T) (hx : T ≤ z.re^2) :
    let E := z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)
    0 ≤ E.re/z.re ∧ E.re/z.re ≤ ∫ t : ℝ, 1/(T-t) ∂μ ∧
      0 ≤ (3*(E.re/z.re)-E.im/z.im)/2 := by
  let f : ℝ → ℂ := fun t => z/(z^2-(t:ℂ))
  have hf : Integrable f μ := by
    simpa [f,div_eq_mul_inv] using (cauchy_kernel_integrable μ hsupp z (hT.trans hx)).const_mul z
  have hE : z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) = ∫ t, f t ∂μ := by
    rw [← integral_const_mul]
    simp only [f,div_eq_mul_inv]
  dsimp only
  rw [hE]
  have hAre : Integrable (fun t => (f t).re/z.re) μ := hf.re.div_const _
  have hBim : Integrable (fun t => (f t).im/z.im) μ := hf.im.div_const _
  have hA : (∫ t, f t ∂μ).re/z.re = ∫ t, (f t).re/z.re ∂μ := by
    rw [integral_div]; exact congrArg (fun v : ℝ => v/z.re) (integral_re hf).symm
  have hB : (∫ t, f t ∂μ).im/z.im = ∫ t, (f t).im/z.im ∂μ := by
    rw [integral_div]; exact congrArg (fun v : ℝ => v/z.im) (integral_im hf).symm
  rw [hA,hB]
  have hparts : ∀ᵐ t ∂μ,
      0 ≤ (f t).re/z.re ∧ (f t).re/z.re ≤ 1/(T-t) ∧
      0 ≤ (3*((f t).re/z.re)-(f t).im/z.im)/2 := by
    filter_upwards [hsupp] with t ht
    obtain ⟨hr,hi⟩ := cauchy_root_kernel_parts z hxpos (hT.trans hx) t ht
    obtain ⟨hd,hAp,_,hCp,hAub⟩ := sextic_kernel_bounds (z.re^2) (z.im^2) t T hT hx (sq_nonneg _) ht.1 ht.2
    have hD : (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4 =
        (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+(z.im^2)^2 := by ring
    dsimp only [f]
    rw [hr,hi]
    simp only [mul_div_cancel_left₀ _ hxpos.ne',neg_mul,neg_div,mul_div_cancel_left₀ _ hypos.ne']
    rw [hD]
    refine ⟨hAp,hAub,?_⟩
    convert hCp using 1 <;> ring
  refine ⟨integral_nonneg_of_ae (hparts.mono fun t ht => ht.1),
    integral_mono_ae hAre (cauchy_real_kernel_integrable μ hsupp T (by linarith))
      (hparts.mono fun t ht => ht.2.1),?_⟩
  have hpos := integral_nonneg_of_ae (hparts.mono fun t ht => ht.2.2)
  simpa only [integral_div,integral_sub (hAre.const_mul 3) hBim,integral_const_mul] using hpos

end DerivativeChainPrivate

end


section
-- Source module: CauchyRootImag


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem cauchy_root_imaginary_bounds (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (z : ℂ) (hxpos : 0 < z.re) (hypos : 0 < z.im)
    (T : ℝ) (hT : 5/2 ≤ T) (hx : T ≤ z.re^2) :
    let E := z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)
    E.im/z.im ≤ 0 ∧ -(1+3/(T-3/2))*(∫ t : ℝ, 1/(T-t) ∂μ) ≤ E.im/z.im := by
  let f : ℝ → ℂ := fun t => z/(z^2-(t:ℂ))
  have hf : Integrable f μ := by
    simpa [f,div_eq_mul_inv] using (cauchy_kernel_integrable μ hsupp z (hT.trans hx)).const_mul z
  have hE : z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ) = ∫ t, f t ∂μ := by
    rw [← integral_const_mul]
    simp only [f,div_eq_mul_inv]
  dsimp only
  rw [hE]
  have hBim : Integrable (fun t => (f t).im/z.im) μ := hf.im.div_const _
  have hB : (∫ t, f t ∂μ).im/z.im = ∫ t, (f t).im/z.im ∂μ := by
    rw [integral_div]; exact congrArg (fun v : ℝ => v/z.im) (integral_im hf).symm
  rw [hB]
  have hparts : ∀ᵐ t ∂μ, (f t).im/z.im ≤ 0 ∧
      -(1+3/(T-3/2))*(1/(T-t)) ≤ (f t).im/z.im := by
    filter_upwards [hsupp] with t ht
    obtain ⟨_,hi⟩ := cauchy_root_kernel_parts z hxpos (hT.trans hx) t ht
    obtain ⟨_,_,hBp,_,_⟩ := sextic_kernel_bounds (z.re^2) (z.im^2) t T hT hx (sq_nonneg _) ht.1 ht.2
    have hBu := sextic_kernel_B_bound (z.re^2) (z.im^2) t T hT hx (sq_nonneg _) ht.1 ht.2
    have hD : (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+z.im^4 =
        (z.re^2-t)^2+2*(z.re^2+t)*z.im^2+(z.im^2)^2 := by ring
    dsimp only [f]
    rw [hi]
    simp only [neg_mul,neg_div,mul_div_cancel_left₀ _ hypos.ne']
    rw [hD]
    constructor <;> linarith
  constructor
  · exact integral_nonpos_of_ae (hparts.mono fun t ht => ht.1)
  · have hb := integral_mono_ae ((cauchy_real_kernel_integrable μ hsupp T (by linarith)).const_mul
        (-(1+3/(T-3/2)))) hBim (hparts.mono fun t ht => ht.2)
    simpa only [integral_const_mul] using hb

end DerivativeChainPrivate

end


section
-- Source module: FifthSexticCorrections


set_option autoImplicit false
namespace DerivativeChainPrivate
open MeasureTheory Set

theorem fifth_sextic_bound_at_seven_halves :
    (7/2:ℝ)+(-35/17)/2-Real.sqrt ((7/2)^2+(-35/17)*(7/2)+490/561+(686/5049)/(7/2)) < 31/1000 := by
  have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ (7/2)^2+(-35/17)*(7/2)+490/561+(686/5049)/(7/2))
  have hp := Real.sqrt_nonneg ((7/2:ℝ)^2+(-35/17)*(7/2)+490/561+(686/5049)/(7/2))
  norm_num at hs hp ⊢
  nlinarith

theorem fifth_sextic_correction_bounds (μ : Measure ℝ) [IsFiniteMeasure μ]
    (hsupp : ∀ᵐ t ∂μ, t ∈ Icc (-1/4:ℝ) (3/2))
    (hμ : ∀ u : ℂ, 0 < u.im → sexticShift (-35/17) (490/561) (686/5049) u =
      TeschlQM.Herglotz.borelTransform μ u)
    (z : ℂ) (hx : 0 < z.re) (hy : 0 < z.im) (hX : 7/2 ≤ z.re^2) :
    let E := ((3*Real.sqrt 1122/182:ℝ):ℂ)*(z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ))
    0 ≤ E.re/z.re ∧ E.re/z.re ≤ 217/12500 ∧ E.im/z.im ≤ 0 ∧
      0 ≤ (3*(E.re/z.re)-E.im/z.im)/2 ∧ (3*(E.re/z.re)-E.im/z.im)/2 ≤ 2387/50000 := by
  let k := 3*Real.sqrt 1122/182
  let E := z*(∫ t : ℝ, (z^2-(t:ℂ))⁻¹ ∂μ)
  let M := ∫ t : ℝ, 1/((7/2)-t) ∂μ
  obtain ⟨hA0,hAM,hC⟩ := cauchy_root_corrections μ hsupp z hx hy (7/2) (by norm_num) hX
  obtain ⟨hB0,hBM⟩ := cauchy_root_imaginary_bounds μ hsupp z hx hy (7/2) (by norm_num) hX
  change 0 ≤ E.re/z.re at hA0
  change E.re/z.re ≤ M at hAM
  change 0 ≤ (3*(E.re/z.re)-E.im/z.im)/2 at hC
  change E.im/z.im ≤ 0 at hB0
  change -(1+3/((7/2:ℝ)-3/2))*M ≤ E.im/z.im at hBM
  norm_num at hBM
  have hk : 0 < k := by dsimp [k]; positivity
  have hku : k < 14/25 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1122)
    have hp := Real.sqrt_nonneg 1122
    dsimp only [k]
    nlinarith
  have hMlt : M < 31/1000 := by
    have hb := sextic_measure_real_value (-35/17) (490/561) (686/5049)
      (by norm_num) (by norm_num) (by norm_num) (by norm_num)
      fifth_sextic_real_exterior μ hsupp hμ (7/2) (by norm_num)
    have ht := real_cauchy_integral_of_borel_value μ (7/2) _ hb
    have he : M = (7/2:ℝ)+(-35/17)/2-
        Real.sqrt ((7/2)^2+(-35/17)*(7/2)+490/561+(686/5049)/(7/2)) := by
      dsimp only [M]; linarith only [ht]
    rw [he]
    exact fifth_sextic_bound_at_seven_halves
  have hM0 : 0 ≤ M := hA0.trans hAM
  have hkM : k*M ≤ 217/12500 := by
    have hp := mul_le_mul hku.le hMlt.le hM0 (by norm_num : (0:ℝ) ≤ 14/25)
    norm_num at hp
    exact hp
  have hAr : ((k:ℂ)*E).re/z.re = k*(E.re/z.re) := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; ring
  have hBi : ((k:ℂ)*E).im/z.im = k*(E.im/z.im) := by
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]; ring
  change 0 ≤ ((k:ℂ)*E).re/z.re ∧ _
  rw [hAr,hBi]
  have hA := mul_le_mul_of_nonneg_left hAM hk.le
  have hB := mul_le_mul_of_nonneg_left hBM hk.le
  have hCC := mul_nonneg hk.le hC
  refine ⟨mul_nonneg hk.le hA0,by linarith,mul_nonpos_of_nonneg_of_nonpos hk.le hB0,?_,?_⟩
  · nlinarith only [hCC]
  · nlinarith only [hA,hB,hkM]

end DerivativeChainPrivate

end


section
-- Source module: FifthSepticScalars

set_option autoImplicit false
namespace DerivativeChainPrivate

theorem fifth_septic_scalar_gaps :
    (29/10:ℝ) < (55-3*Real.sqrt 209)/4 ∧ (55-3*Real.sqrt 209)/4 < 3 ∧
    (12/5:ℝ) < 55-3*Real.sqrt 1122/2 ∧ (55-3*Real.sqrt 209)/4 < 55-3*Real.sqrt 1122/2 ∧
    (5/8:ℝ) < (10-15*Real.sqrt 1122/68)-(5-4*Real.sqrt 209/19) ∧
    (263/1000:ℝ) < (5-4*Real.sqrt 209/19)-(29/50)*((55-3*Real.sqrt 209)/4) ∧
    (237/1160:ℝ) < (5-4*Real.sqrt 209/19)-(3/5)*((55-3*Real.sqrt 209)/4) ∧
    (24:ℝ) < (55+3*Real.sqrt 209)/4 ∧ (5+4*Real.sqrt 209/19) < 9 := by
  have h1 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 209)
  have p1 := Real.sqrt_nonneg 209
  have h2 := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1122)
  have p2 := Real.sqrt_nonneg 1122
  have l1 : (144568:ℝ)/10000 < Real.sqrt 209 := by nlinarith only [h1,p1]
  have u1 : Real.sqrt 209 < (144569:ℝ)/10000 := by nlinarith only [h1,p1]
  have l2 : (334962:ℝ)/10000 < Real.sqrt 1122 := by nlinarith only [h2,p2]
  have u2 : Real.sqrt 1122 < (334963:ℝ)/10000 := by nlinarith only [h2,p2]
  refine ⟨?_,?_,?_,?_,?_,?_,?_,?_,?_⟩ <;> linarith only [l1,u1,l2,u2]
end DerivativeChainPrivate

end


section
-- Source module: FifthAffineRows

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem fifth_old_unit_composition (β : ℂ) :
    let r := Real.sqrt 7
    let γ := ((13*(1/r):ℝ):ℂ)*β
    (X^3-C 7*X-91*C β : Polynomial ℂ).comp (C 0+C (r:ℂ)*X) =
      C ((r:ℂ)^3)*(X^3-X-C γ) := by
  let r := Real.sqrt 7
  let γ := ((13*(1/r):ℝ):ℂ)*β
  have hr : 0 < r := by dsimp [r]; positivity
  have hrr : (r:ℂ) ≠ 0 := by exact_mod_cast hr.ne'
  have hr2 : (r:ℂ)^2=7 := by
    dsimp [r]
    rw [← Complex.ofReal_pow,Real.sq_sqrt (by norm_num)]
    norm_num
  have hr3 : (r:ℂ)^3=7*(r:ℂ) := by calc
    _ = (r:ℂ)^2*(r:ℂ) := by ring
    _ = _ := by rw [hr2]
  have hrγ : (r:ℂ)^3*γ=91*β := by
    rw [hr3]
    dsimp [γ]
    push_cast
    field_simp <;> ring
  change (X^3-C 7*X-91*C β : Polynomial ℂ).comp (C 0+C (r:ℂ)*X) = C ((r:ℂ)^3)*(X^3-X-C γ)
  apply Polynomial.funext
  intro z
  simp only [eval_comp,eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat,zero_add]
  linear_combination z*hr3+hrγ

theorem fifth_unit_root_to_old (β z : ℂ) (k : ℕ)
    (hz : (derivative^[k] ((X^3-X-C (((13*(1/Real.sqrt 7):ℝ):ℂ)*β))^5 : Polynomial ℂ)).eval z=0) :
    (derivative^[k] ((X^3-C 7*X-91*C β)^5 : Polynomial ℂ)).eval ((Real.sqrt 7:ℂ)*z)=0 := by
  let r := Real.sqrt 7
  let γ := ((13*(1/r):ℝ):ℂ)*β
  have hr : (r:ℂ) ≠ 0 := by
    have hh : (r:ℝ) ≠ 0 := ne_of_gt (Real.sqrt_pos.mpr (by norm_num))
    exact_mod_cast hh
  have hq := fifth_old_unit_composition β
  change (X^3-C 7*X-91*C β : Polynomial ℂ).comp (C 0+C (r:ℂ)*X) = C ((r:ℂ)^3)*(X^3-X-C γ) at hq
  have hp : ((X^3-C 7*X-91*C β)^5 : Polynomial ℂ).comp (C 0+C (r:ℂ)*X) =
      C (((r:ℂ)^3)^5)*(X^3-X-C γ)^5 := by
    rw [Polynomial.pow_comp,hq,mul_pow,← Polynomial.C_pow]
  have hh := affine_derivative_root ((X^3-C 7*X-91*C β)^5) ((X^3-X-C γ)^5)
    0 (r:ℂ) (((r:ℂ)^3)^5) hr hp k z hz
  simpa only [zero_add] using hh

theorem fifth_unit_source_to_old (β z : ℂ)
    (hz : z^3-z-((13*(1/Real.sqrt 7):ℝ):ℂ)*β=0) :
    ((Real.sqrt 7:ℂ)*z)^3-7*((Real.sqrt 7:ℂ)*z)-91*β=0 := by
  have hh := congrArg (fun p : Polynomial ℂ => p.eval z) (fifth_old_unit_composition β)
  simp only [eval_comp,eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat,zero_add] at hh
  rw [hz,mul_zero] at hh
  exact hh
end DerivativeChainPrivate

end


section
-- Source module: FifthUnitRows

set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial
theorem fifth_unit_expansion (β : ℂ) : ((X^3-X-C β)^5 : Polynomial ℂ) =
    C ((1)*β^0)*X^15+
    C ((-5)*β^0)*X^13+
    C ((-5)*β^1)*X^12+
    C ((10)*β^0)*X^11+
    C ((20)*β^1)*X^10+
    C ((10)*β^2+(-10)*β^0)*X^9+
    C ((-30)*β^1)*X^8+
    C ((-30)*β^2+(5)*β^0)*X^7+
    C ((-10)*β^3+(20)*β^1)*X^6+
    C ((30)*β^2+(-1)*β^0)*X^5+
    C ((20)*β^3+(-5)*β^1)*X^4+
    C ((5)*β^4+(-10)*β^2)*X^3+
    C ((-10)*β^3)*X^2+
    C ((-5)*β^4)*X^1+
    C ((-1)*β^5)*X^0 := by
  apply Polynomial.funext
  intro z
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat]
  ring

 

 

theorem fifth_unit_row_7 (β z : ℂ) :
    (derivative^[8] ((X^3-X-C β)^5 : Polynomial ℂ)).eval z =
      259459200*((1)*β^0*z^7+(-1)*β^0*z^5+(-5/13)*β^1*z^4+(10/39)*β^0*z^3+(20/143)*β^1*z^2+(2/143)*β^2*z^1+(-2/143)*β^0*z^1+(-2/429)*β^1*z^0) := by
  rw [fifth_unit_expansion]
  simp only [iterate_map_add,iterate_derivative_C_mul,iterate_derivative_X_pow_eq_C_mul,
    eval_add,eval_mul,eval_C,eval_pow,eval_X]
  norm_num [Nat.descFactorial] <;> ring
theorem fifth_unit_row_8 (β z : ℂ) :
    (derivative^[7] ((X^3-X-C β)^5 : Polynomial ℂ)).eval z =
      32432400*((1)*β^0*z^8+(-4/3)*β^0*z^6+(-8/13)*β^1*z^5+(20/39)*β^0*z^4+(160/429)*β^1*z^3+(8/143)*β^2*z^2+(-8/143)*β^0*z^2+(-16/429)*β^1*z^1+(-2/429)*β^2*z^0+(1/1287)*β^0*z^0) := by
  rw [fifth_unit_expansion]
  simp only [iterate_map_add,iterate_derivative_C_mul,iterate_derivative_X_pow_eq_C_mul,
    eval_add,eval_mul,eval_C,eval_pow,eval_X]
  norm_num [Nat.descFactorial] <;> ring
theorem fifth_unit_row_9 (β z : ℂ) :
    (derivative^[6] ((X^3-X-C β)^5 : Polynomial ℂ)).eval z =
      3603600*((1)*β^0*z^9+(-12/7)*β^0*z^7+(-12/13)*β^1*z^6+(12/13)*β^0*z^5+(120/143)*β^1*z^4+(24/143)*β^2*z^3+(-24/143)*β^0*z^3+(-24/143)*β^1*z^2+(-6/143)*β^2*z^1+(1/143)*β^0*z^1+(-2/1001)*β^3*z^0+(4/1001)*β^1*z^0) := by
  rw [fifth_unit_expansion]
  simp only [iterate_map_add,iterate_derivative_C_mul,iterate_derivative_X_pow_eq_C_mul,
    eval_add,eval_mul,eval_C,eval_pow,eval_X]
  norm_num [Nat.descFactorial] <;> ring
theorem fifth_unit_row_10 (β z : ℂ) :
    (derivative^[5] ((X^3-X-C β)^5 : Polynomial ℂ)).eval z =
      360360*((1)*β^0*z^10+(-15/7)*β^0*z^8+(-120/91)*β^1*z^7+(20/13)*β^0*z^6+(240/143)*β^1*z^5+(60/143)*β^2*z^4+(-60/143)*β^0*z^4+(-80/143)*β^1*z^3+(-30/143)*β^2*z^2+(5/143)*β^0*z^2+(-20/1001)*β^3*z^1+(40/1001)*β^1*z^1+(10/1001)*β^2*z^0+(-1/3003)*β^0*z^0) := by
  rw [fifth_unit_expansion]
  simp only [iterate_map_add,iterate_derivative_C_mul,iterate_derivative_X_pow_eq_C_mul,
    eval_add,eval_mul,eval_C,eval_pow,eval_X]
  norm_num [Nat.descFactorial] <;> ring
end DerivativeChainPrivate

end


section
-- Source module: FifthCubicRows

set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial









theorem fifth_source_decic_row (β z : ℂ) :
    (derivative^[5] ((X^3-X-C β)^5 : Polynomial ℂ)).eval z=360360*(fifthUnitP10 β).eval z := by
  rw [fifth_unit_row_10]
  norm_num [fifthUnitP10]
  ring
end DerivativeChainPrivate

end


section
-- Source module: FifthSexticRescale

set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate

theorem fifth_sextic_unit_rescale (β w E : ℂ) (hR : 0 ≤ β.re) (hx : 0 < w.re) (hy : 0 < w.im)
    (hX : 7/2 ≤ w.re^2)
    (hroot : (182/11)*β^2-20*β*w^3+(280/11)*β*w+w^6-5*w^4+(70/13)*w^2-98/143=0)
    (hgraph : β/w=(((110-3*Real.sqrt 1122)/182:ℝ):ℂ)*w^2-(((680-15*Real.sqrt 1122)/884:ℝ):ℂ)+E/w)
    (hA : E.re/w.re ≤ 217/12500) (hB : E.im/w.im ≤ 0)
    (hC : (3*(E.re/w.re)-E.im/w.im)/2 ≤ 2387/50000) :
    let c : ℝ := 1/Real.sqrt 7
    let γ := ((13*c:ℝ):ℂ)*β
    let v := (c:ℂ)*w
    let e := ((13*c:ℝ):ℂ)*E
    0 < v.re ∧ 0 < v.im ∧ 1/2 ≤ v.re^2 ∧
      (2/1001)*γ^2-(20/91)*γ*v^3+(40/1001)*γ*v+v^6-(5/7)*v^4+(10/91)*v^2-2/1001=0 ∧
      γ/v=((55-3*Real.sqrt 1122/2:ℝ):ℂ)*v^2-((10-15*Real.sqrt 1122/68:ℝ):ℂ)+e/v ∧
      e.re/v.re ≤ 2821/12500 ∧ e.im/v.im ≤ 0 ∧
      (3*(e.re/v.re)-e.im/v.im)/2 ≤ 5/8 ∧ 1/2 ≤ v.re^2-3*v.im^2 := by
  let c : ℝ := 1/Real.sqrt 7
  let γ := ((13*c:ℝ):ℂ)*β
  let v := (c:ℂ)*w
  let e := ((13*c:ℝ):ℂ)*E
  have hc : 0 < c := by dsimp [c]; positivity
  have hc2 : c^2=1/7 := by dsimp [c]; rw [div_pow,Real.sq_sqrt (by norm_num)]; norm_num
  have hcc : (c:ℂ) ≠ 0 := by exact_mod_cast hc.ne'
  have hcc2 : (c:ℂ)^2=1/7 := by rw [← Complex.ofReal_pow,hc2]; norm_num
  have hcc4 : (c:ℂ)^4=1/49 := by calc
    _ = ((c:ℂ)^2)^2 := by ring
    _ = _ := by rw [hcc2]; norm_num
  have hcc6 : (c:ℂ)^6=1/343 := by calc
    _ = ((c:ℂ)^2)^3 := by ring
    _ = _ := by rw [hcc2]; norm_num
  have hw : w ≠ 0 := by intro he; simp [he] at hx
  have hvr : v.re=c*w.re := by simp [v,Complex.mul_re]
  have hvi : v.im=c*w.im := by simp [v,Complex.mul_im]
  have hvx : 0 < v.re := by rw [hvr]; positivity
  have hvy : 0 < v.im := by rw [hvi]; positivity
  have hvX : 1/2 ≤ v.re^2 := by rw [hvr,mul_pow,hc2]; nlinarith only [hX]
  have hscale : (2/1001)*γ^2-(20/91)*γ*v^3+(40/1001)*γ*v+v^6-(5/7)*v^4+(10/91)*v^2-2/1001 =
      (1/343:ℂ)*((182/11)*β^2-20*β*w^3+(280/11)*β*w+w^6-5*w^4+(70/13)*w^2-98/143) := by
    dsimp only [γ,v]
    push_cast
    ring_nf
    rw [hcc2,hcc4,hcc6]
    ring
  have hrootv : (2/1001)*γ^2-(20/91)*γ*v^3+(40/1001)*γ*v+v^6-(5/7)*v^4+(10/91)*v^2-2/1001=0 := by rw [hscale,hroot,mul_zero]
  have hgv : γ/v=((55-3*Real.sqrt 1122/2:ℝ):ℂ)*v^2-((10-15*Real.sqrt 1122/68:ℝ):ℂ)+e/v := by
    calc
      _ = 13*(β/w) := by dsimp [γ,v]; push_cast; field_simp <;> ring
      _ = _ := by
        rw [hgraph]
        dsimp only [v,e]
        push_cast
        rw [mul_pow,hcc2]
        field_simp <;> ring
  have hAv : e.re/v.re=13*(E.re/w.re) := by
    dsimp only [e,v]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    field_simp <;> ring
  have hBv : e.im/v.im=13*(E.im/w.im) := by
    dsimp only [e,v]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    field_simp <;> ring
  have hAu : e.re/v.re ≤ 2821/12500 := by rw [hAv]; linarith only [hA]
  have hBu : e.im/v.im ≤ 0 := by rw [hBv]; linarith only [hB]
  have hCu : (3*(e.re/v.re)-e.im/v.im)/2 ≤ 5/8 := by rw [hAv,hBv]; linarith only [hC]
  change 0 < v.re ∧ _
  refine ⟨hvx,hvy,hvX,hrootv,hgv,hAu,hBu,hCu,?_⟩
  have hγ : 0 ≤ γ.re := by simp only [γ,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; positivity
  have hv : v ≠ 0 := mul_ne_zero hcc hw
  have hr := (cubic_graph_coordinate_parts γ v e (55-3*Real.sqrt 1122/2) (10-15*Real.sqrt 1122/68) hv hgv).1
  have hRp : γ.re/v.re=(55-3*Real.sqrt 1122/2)*(v.re^2-3*v.im^2)-(10-15*Real.sqrt 1122/68)+e.re/v.re := by rw [hr]; field_simp
  have hnonneg : 0 ≤ γ.re/v.re := div_nonneg hγ hvx.le
  rw [hRp] at hnonneg
  have ha := fifth_septic_scalar_gaps.2.2.1
  have hslack : (2821/12500:ℝ) < (10-15*Real.sqrt 1122/68)-(55-3*Real.sqrt 1122/2)/2 := by
    have hs := Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 1122)
    have hp := Real.sqrt_nonneg 1122
    nlinarith only [hs,hp]
  have ht : (55-3*Real.sqrt 1122/2)*(1/2) < (55-3*Real.sqrt 1122/2)*(v.re^2-3*v.im^2) := by linarith only [hslack,hAu,hnonneg]
  exact (lt_of_mul_lt_mul_left ht (by linarith only [ha])).le
end DerivativeChainPrivate

end

open DerivativeChainPrivate in
theorem solution (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im) :
    ∃ z : Fin 15 → ℂ,
      (∀ i, (derivative^[15-(i.val+1)] ((X^3-C 7*X-91*C β)^5)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin 15, 10 ≤ i.val → z i=z 14) ∧
      (z 14)^3-7*z 14-91*β=0 ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2*‖z 14‖ := by
  obtain ⟨f,hfroot,hf0,hfr,hfi,hfpos,hfX,hfinv⟩ := normalized_fifth_prefix_five β hR hI.le
  have hfim : 0 ≤ (f 4).im := by
    have hh := hfi (show (0:Fin 5) ≤ 4 by decide)
    simpa only [hf0,Complex.zero_im] using hh
  have hfQ : (f 4)^5-(10/3)*(f 4)^3-10*β*(f 4)^2+(70/39)*(f 4)+(140/33)*β=0 := by
    have hh := hfroot 4
    change (derivative^[10] ((X^3-C 7*X-91*C β)^5)).eval (f 4)=0 at hh
    rw [(normalized_fifth_power_actual_rows β (f 4)).2.2.2.2.2.1] at hh
    linear_combination (1/10897286400:ℂ)*hh
  obtain ⟨μ,hfinite,hsupp,hμ,w₆,hw₆,h₅₆r,h₅₆i,h₆i,h₆loc,h₆graph⟩ :=
    normalized_fifth_selected_sextic_step β (f 4) hR hI hfpos hfim hfX hfQ hfinv
  letI : IsFiniteMeasure μ := hfinite
  have h₆r : 0 < w₆.re := lt_of_lt_of_le hfpos h₅₆r
  have hw₆ne : w₆ ≠ 0 := by intro he; simp [he] at h₆r
  let E₆ := ((3*Real.sqrt 1122/182:ℝ):ℂ)*(w₆*(∫ t : ℝ, (w₆^2-(t:ℂ))⁻¹ ∂μ))
  have hEgraph : β/w₆=(((110-3*Real.sqrt 1122)/182:ℝ):ℂ)*w₆^2-(((680-15*Real.sqrt 1122)/884:ℝ):ℂ)+E₆/w₆ := by
    convert h₆graph using 1
    dsimp [E₆]
    field_simp
  obtain ⟨_,hA₆,hB₆,_,hC₆⟩ := fifth_sextic_correction_bounds μ hsupp hμ w₆ h₆r h₆i h₆loc.le
  let r := Real.sqrt 7
  let c := 1/Real.sqrt 7
  let γ := ((13*c:ℝ):ℂ)*β
  let v₆ := (c:ℂ)*w₆
  let e₆ := ((13*c:ℝ):ℂ)*E₆
  have hr : 0 < r := by dsimp [r]; positivity
  have hc : 0 < c := by dsimp [c]; positivity
  have hγR : 0 ≤ γ.re := by simp only [γ,Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]; positivity
  have hγI : 0 < γ.im := by simp only [γ,Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]; positivity
  obtain ⟨hv₆r,hv₆i,hv₆X,hv₆root,hv₆graph,hv₆A,hv₆B,hv₆C,hv₆W⟩ :=
    fifth_sextic_unit_rescale β w₆ E₆ hR h₆r h₆i h₆loc.le hw₆ hEgraph hA₆ hB₆ hC₆
  obtain ⟨v₇,hv₇,h₆₇r,h₆₇i,h₇X,h₇graph,h₇A,h₇B,h₇C,h₇W⟩ := normalized_fifth_septic_step_with_bounds γ v₆ e₆ hγR hγI hv₆r hv₆i hv₆X
    hv₆root hv₆graph hv₆A hv₆B hv₆C hv₆W
  have h₇r : 0 < v₇.re := lt_of_lt_of_le hv₆r h₆₇r
  have h₇i : 0 < v₇.im := lt_of_lt_of_le hv₆i h₆₇i
  obtain ⟨v₈,hv₈,h₇₈r,h₇₈i,h₈X,h₈graph⟩ := normalized_fifth_octic_step_with_bounds γ v₇ hγR hγI h₇r h₇i h₇X.le hv₇ h₇graph h₇A h₇B h₇C h₇W
  have h₈r : 0 < v₈.re := lt_of_lt_of_le h₇r h₇₈r
  have h₈i : 0 < v₈.im := lt_of_lt_of_le h₇i h₇₈i
  obtain ⟨v₉,α₉,b₉,e₉,hv₉,h₈₉r,h₈₉i,h₉X,h₉αlo,h₉αhi,h₉blo,h₉bhi,h₉graph,h₉A,h₉B,h₉C,h₉W⟩ :=
    normalized_fifth_nonic_step γ v₈ hγR hγI h₈r h₈i h₈X.le hv₈ h₈graph
  have h₉r : 0 < v₉.re := lt_of_lt_of_le h₈r h₈₉r
  have h₉i : 0 < v₉.im := lt_of_lt_of_le h₈i h₈₉i
  obtain ⟨v₁₀,α₁₀,b₁₀,e₁₀,hv₁₀,h₉₁₀r,h₉₁₀i,h₁₀αlo,h₁₀αhi,h₁₀blo,h₁₀bhi,h₁₀graph,h₁₀A,h₁₀B,h₁₀C⟩ :=
    normalized_fifth_decic_step γ v₉ e₉ α₉ b₉ hγR hγI h₉r h₉i h₉X.le hv₉ h₉αlo h₉αhi h₉blo h₉bhi h₉graph h₉A h₉B h₉C h₉W
  have h₁₀r : 0 < v₁₀.re := lt_of_lt_of_le h₉r h₉₁₀r
  have h₁₀i : 0 < v₁₀.im := lt_of_lt_of_le h₉i h₉₁₀i
  obtain ⟨ρ,hρ,h₁₀ρr,h₁₀ρi⟩ := normalized_fifth_source_step γ v₁₀ e₁₀ α₁₀ b₁₀ hγR hγI h₁₀r h₁₀i hv₁₀ h₁₀αlo h₁₀blo h₁₀graph h₁₀C
  have hrc : r*c=1 := by dsimp [r,c]; field_simp
  have hback : (r:ℂ)*v₆=w₆ := by
    dsimp only [v₆]
    rw [← mul_assoc,← Complex.ofReal_mul,hrc,Complex.ofReal_one,one_mul]
  have scale_re (x y : ℂ) (h : x.re ≤ y.re) : ((r:ℂ)*x).re ≤ ((r:ℂ)*y).re := by
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    exact mul_le_mul_of_nonneg_left h hr.le
  have scale_im (x y : ℂ) (h : x.im ≤ y.im) : ((r:ℂ)*x).im ≤ ((r:ℂ)*y).im := by
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    exact mul_le_mul_of_nonneg_left h hr.le
  let g : ℕ → ℂ
    | 0 => f 0
    | 1 => f 1
    | 2 => f 2
    | 3 => f 3
    | 4 => f 4
    | 5 => w₆
    | 6 => (r:ℂ)*v₇
    | 7 => (r:ℂ)*v₈
    | 8 => (r:ℂ)*v₉
    | 9 => (r:ℂ)*v₁₀
    | _ => (r:ℂ)*ρ
  have hre : ∀ i < 14, (g i).re ≤ (g (i+1)).re := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfr (by decide : (0:Fin 5) ≤ 1)
    · exact hfr (by decide : (1:Fin 5) ≤ 2)
    · exact hfr (by decide : (2:Fin 5) ≤ 3)
    · exact hfr (by decide : (3:Fin 5) ≤ 4)
    · exact h₅₆r
    · simpa only [hback] using scale_re v₆ v₇ h₆₇r
    · exact scale_re v₇ v₈ h₇₈r
    · exact scale_re v₈ v₉ h₈₉r
    · exact scale_re v₉ v₁₀ h₉₁₀r
    · exact scale_re v₁₀ ρ h₁₀ρr
    all_goals exact le_rfl
  have him : ∀ i < 14, (g i).im ≤ (g (i+1)).im := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfi (by decide : (0:Fin 5) ≤ 1)
    · exact hfi (by decide : (1:Fin 5) ≤ 2)
    · exact hfi (by decide : (2:Fin 5) ≤ 3)
    · exact hfi (by decide : (3:Fin 5) ≤ 4)
    · exact h₅₆i
    · simpa only [hback] using scale_im v₆ v₇ h₆₇i
    · exact scale_im v₇ v₈ h₇₈i
    · exact scale_im v₈ v₉ h₈₉i
    · exact scale_im v₉ v₁₀ h₉₁₀i
    · exact scale_im v₁₀ ρ h₁₀ρi
    all_goals exact le_rfl
  have hρold : ((r:ℂ)*ρ)^3-7*((r:ℂ)*ρ)-91*β=0 := fifth_unit_source_to_old β ρ hρ
  have hqρ : (X^3-C 7*X-91*C β : Polynomial ℂ).eval ((r:ℂ)*ρ)=0 := by
    simpa only [eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat] using hρold
  have hrows (i : ℕ) (hi : i < 15) :
      (derivative^[15-(i+1)] ((X^3-C 7*X-91*C β)^5)).eval (g i)=0 := by
    interval_cases i
    · simpa [g] using hfroot 0
    · simpa [g] using hfroot 1
    · simpa [g] using hfroot 2
    · simpa [g] using hfroot 3
    · simpa [g] using hfroot 4
    · rw [(normalized_fifth_power_actual_rows β (g 5)).2.2.2.2.1]
      simp only [g]
      linear_combination 1816214400*hw₆
    · apply fifth_unit_root_to_old β v₇ 8
      change (derivative^[8] ((X^3-X-C γ)^5)).eval v₇=0
      rw [fifth_unit_row_7]
      linear_combination 259459200*hv₇
    · apply fifth_unit_root_to_old β v₈ 7
      change (derivative^[7] ((X^3-X-C γ)^5)).eval v₈=0
      rw [fifth_unit_row_8]
      linear_combination 32432400*hv₈
    · apply fifth_unit_root_to_old β v₉ 6
      change (derivative^[6] ((X^3-X-C γ)^5)).eval v₉=0
      rw [fifth_unit_row_9]
      have hh := hv₉
      norm_num [fifthUnitP9] at hh
      linear_combination 3603600*hh
    · apply fifth_unit_root_to_old β v₁₀ 5
      change (derivative^[5] ((X^3-X-C γ)^5)).eval v₁₀=0
      rw [fifth_source_decic_row,hv₁₀,mul_zero]
    · exact power_root_inherited_derivative _ 5 4 ((r:ℂ)*ρ) hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 5 3 ((r:ℂ)*ρ) hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 5 2 ((r:ℂ)*ρ) hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 5 1 ((r:ℂ)*ρ) hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 5 0 ((r:ℂ)*ρ) hqρ (by norm_num)
  refine ⟨fun i => g i.val,fun i => hrows i.val i.isLt,hf0,?_,hρold,?_,?_,?_⟩
  · intro i hi
    fin_cases i <;> norm_num at hi <;> rfl
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt
  · simpa only [g,hf0,sub_zero,Nat.reduceSub] using northeast_chain_cost 15 g hre him
