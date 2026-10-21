-- Prove2me | solution 1 for DerivativeChainPrivate.cubicFourthChainRadius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-20T16:10:37.578689+00:00
-- url     : https://prove2.me/submissions/5a332c47-2fd7-499b-b3f5-6db33c87c9bc

import Definitions.Def_DerivativeChainPrivate_foundations
import Definitions.Def_DerivativeChainPrivate_higher_power_radicals
import Definitions.Def_TeschlQM_Herglotz_borelTransform
import Mathlib
import Theorems.Thm_DerivativeChainPrivate_normalized_fourth_octic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fourth_selected_sextic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fourth_septic_step
import Theorems.Thm_DerivativeChainPrivate_normalized_fourth_source_step
open Polynomial MeasureTheory Filter Set DerivativeChainPrivate
open scoped Topology
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false


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
-- Source module: Rows


set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_fourth_power_expansion (β : ℂ) :
    ((X^3 - C (11/2) * X - 55 * C β)^4 : Polynomial ℂ) =
      C (1) * X^12 +
      C (-22) * X^10 +
      C (-220*β) * X^9 +
      C (363/2) * X^8 +
      C (3630*β) * X^7 +
      C (18150*β^2 - 1331/2) * X^6 +
      C (-19965*β) * X^5 +
      C (14641/16 - 199650*β^2) * X^4 +
      C (-665500*β^3 + 73205*β/2) * X^3 +
      C (1098075*β^2/2) * X^2 +
      C (3660250*β^3) * X^1 +
      C (9150625*β^4) * X^0 := by
  apply Polynomial.funext
  intro z
  simp only [eval_add,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat]
  ring

theorem normalized_fourth_power_actual_rows (β z : ℂ) :
    let p : Polynomial ℂ := (X^3 - C (11/2) * X - 55 * C β)^4
    (derivative^[4] p).eval z = 11880 * (550*β^2*z^2 - 1210*β^2/3 - 56*β*z^5 + 770*β*z^3/3 - 605*β*z/3 + z^8 - 28*z^6/3 + 77*z^4/3 - 121*z^2/6 + 1331/720) ∧
    (derivative^[5] p).eval z = 95040 * (275*β^2*z/2 - 35*β*z^4 + 385*β*z^2/4 - 605*β/24 + z^7 - 7*z^5 + 77*z^3/6 - 121*z/24) ∧
    (derivative^[6] p).eval z = 665280 * (275*β^2/14 - 20*β*z^3 + 55*β*z/2 + z^6 - 5*z^4 + 11*z^2/2 - 121/168) ∧
    (derivative^[7] p).eval z = 3991680 * (-10*β*z^2 + 55*β/12 + z^5 - 10*z^3/3 + 11*z/6) ∧
    (derivative^[8] p).eval z = 19958400 * (-4*β*z + z^4 - 2*z^2 + 11/30) ∧
    (derivative^[9] p).eval z = 79833600 * (-β + z^3 - z) ∧
    (derivative^[10] p).eval z = 239500800 * (z^2 - 1/3) ∧
    (derivative^[11] p).eval z = 479001600 * (z) := by
  let p : Polynomial ℂ := (X^3 - C (11/2) * X - 55 * C β)^4
  have hexpand := normalized_fourth_power_expansion β
  change p = _ at hexpand
  dsimp only
  refine ⟨?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ,?_ ⟩
  all_goals change (derivative^[_] p).eval z = _
  all_goals rw [hexpand]
  all_goals simp only [iterate_map_add, iterate_derivative_C_mul,
    iterate_derivative_X_pow_eq_C_mul, eval_add, eval_mul, eval_C, eval_pow, eval_X]
  all_goals norm_num [Nat.descFactorial] <;> ring





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

theorem normalized_fourth_prefix_five (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin 5 → ℂ,
      (∀ i, (derivative^[12-(i.val+1)] ((X^3-C (11/2)*X-55*C β)^4)).eval (z i) = 0) ∧
      z 0 = 0 ∧ Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      0 < (z 4).re ∧ 5/2 ≤ (z 4).re^2 ∧
      β / z 4 = (1/10 : ℂ)*(z 4)^2-(23/80)+(33/640)/((z 4)^2-(11/24)) := by
  obtain ⟨w₃,hw₃,_⟩ := normalized_cubic_quadrant_root β hR hI
  obtain ⟨hw₃re,hw₃im,_⟩ := normalized_cubic_positive_root_sector β w₃ hR hI hw₃.1 hw₃.2
  obtain ⟨w₄,hw₄,h₃₄r,h₃₄i,hw₄X,hw₄inv⟩ :=
    normalized_quartic_step (11/30) (by norm_num) (by norm_num) β w₃ hR hI hw₃.1 hw₃.2
  have hw₄pos : 0 < w₄.re := lt_of_lt_of_le hw₃.2 h₃₄r
  obtain ⟨w₅,hw₅,h₄₅r,h₄₅i,hw₅X,hw₅inv⟩ :=
    normalized_quintic_step (11/30) (11/24) (23/80) (33/640)
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
      (derivative^[12-(i+1)] ((X^3-C (11/2)*X-55*C β)^4)).eval (g i) = 0 := by
    interval_cases i
    · rw [(normalized_fourth_power_actual_rows β (g 0)).2.2.2.2.2.2.2]
      simp only [g,mul_zero]
    · rw [(normalized_fourth_power_actual_rows β (g 1)).2.2.2.2.2.2.1]
      simp only [g,hrc]
      norm_num
    · rw [(normalized_fourth_power_actual_rows β (g 2)).2.2.2.2.2.1]
      simp only [g]
      linear_combination 79833600 * hw₃.1
    · rw [(normalized_fourth_power_actual_rows β (g 3)).2.2.2.2.1]
      simp only [g]
      linear_combination 19958400 * hw₄
    · rw [(normalized_fourth_power_actual_rows β (g 4)).2.2.2.1]
      simp only [g]
      linear_combination 3991680 * hw₅
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
-- Source module: FourthNormalizedChain


set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial MeasureTheory

theorem normalized_fourth_chain_strict (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 < β.im) :
    ∃ z : Fin 12 → ℂ,
      (∀ i, (derivative^[12-(i.val+1)] ((X^3-C (11/2)*X-55*C β)^4)).eval (z i)=0) ∧
      z 0=0 ∧ (∀ i : Fin 12, 8 ≤ i.val → z i=z 11) ∧
      (z 11)^3-(11/2)*z 11-55*β=0 ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2*‖z 11‖ := by
  obtain ⟨f,hfroot,hf0,hfr,hfi,hfpos,hfX,hfinv⟩ := normalized_fourth_prefix_five β hR hI.le
  have hfim : 0 ≤ (f 4).im := by
    have hh := hfi (show (0:Fin 5) ≤ 4 by decide)
    simpa only [hf0,Complex.zero_im] using hh
  have hfQ : (f 4)^5-(10/3)*(f 4)^3-10*β*(f 4)^2+(11/6)*(f 4)+(55/12)*β=0 := by
    have hh := hfroot 4
    change (derivative^[7] ((X^3-C (11/2)*X-55*C β)^4)).eval (f 4)=0 at hh
    rw [(normalized_fourth_power_actual_rows β (f 4)).2.2.2.1] at hh
    linear_combination (1/3991680:ℂ)*hh
  obtain ⟨μ,hfinite,hsupp,hμ,w₆,hw₆,h₅₆r,h₅₆i,h₆i,h₆loc,h₆graph⟩ :=
    normalized_fourth_selected_sextic_step β (f 4) hR hI hfpos hfim hfX hfQ hfinv
  letI : IsFiniteMeasure μ := hfinite
  have h₆r : 0 < w₆.re := lt_of_lt_of_le hfpos h₅₆r
  obtain ⟨w₇,hw₇,h₆₇r,h₆₇i,h₇X,h₇graph⟩ := normalized_fourth_septic_step μ hsupp hμ β w₆ hR hI h₆r h₆i h₆loc.le hw₆ h₆graph
  have h₇r : 0 < w₇.re := lt_of_lt_of_le h₆r h₆₇r
  have h₇i : 0 < w₇.im := lt_of_lt_of_le h₆i h₆₇i
  obtain ⟨w₈,hw₈,h₇₈r,h₇₈i,h₈graph⟩ := normalized_fourth_octic_step β w₇ hR hI h₇r h₇i h₇X.le hw₇ h₇graph
  have h₈r : 0 < w₈.re := lt_of_lt_of_le h₇r h₇₈r
  have h₈i : 0 < w₈.im := lt_of_lt_of_le h₇i h₇₈i
  have h₈X : 4 ≤ w₈.re^2 := by nlinarith only [h₇X,h₇r,h₇₈r]
  obtain ⟨ρ,hρ,h₈ρr,h₈ρi⟩ := normalized_fourth_source_step β w₈ hR hI h₈r h₈i h₈X hw₈ h₈graph
  let g : ℕ → ℂ
    | 0 => f 0
    | 1 => f 1
    | 2 => f 2
    | 3 => f 3
    | 4 => f 4
    | 5 => w₆
    | 6 => w₇
    | 7 => w₈
    | _ => ρ
  have hre : ∀ i < 11, (g i).re ≤ (g (i+1)).re := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfr (by decide : (0:Fin 5) ≤ 1)
    · exact hfr (by decide : (1:Fin 5) ≤ 2)
    · exact hfr (by decide : (2:Fin 5) ≤ 3)
    · exact hfr (by decide : (3:Fin 5) ≤ 4)
    · exact h₅₆r
    · exact h₆₇r
    · exact h₇₈r
    · exact h₈ρr
    all_goals exact le_rfl
  have him : ∀ i < 11, (g i).im ≤ (g (i+1)).im := by
    intro i hi
    interval_cases i <;> simp only [g]
    · exact hfi (by decide : (0:Fin 5) ≤ 1)
    · exact hfi (by decide : (1:Fin 5) ≤ 2)
    · exact hfi (by decide : (2:Fin 5) ≤ 3)
    · exact hfi (by decide : (3:Fin 5) ≤ 4)
    · exact h₅₆i
    · exact h₆₇i
    · exact h₇₈i
    · exact h₈ρi
    all_goals exact le_rfl
  have hqρ : (X^3-C (11/2)*X-55*C β : Polynomial ℂ).eval ρ=0 := by
    simpa only [eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat] using hρ
  have hrows (i : ℕ) (hi : i < 12) :
      (derivative^[12-(i+1)] ((X^3-C (11/2)*X-55*C β)^4)).eval (g i)=0 := by
    interval_cases i
    · simpa [g] using hfroot 0
    · simpa [g] using hfroot 1
    · simpa [g] using hfroot 2
    · simpa [g] using hfroot 3
    · simpa [g] using hfroot 4
    · rw [(normalized_fourth_power_actual_rows β (g 5)).2.2.1]
      simp only [g]
      linear_combination 665280*hw₆
    · rw [(normalized_fourth_power_actual_rows β (g 6)).2.1]
      simp only [g]
      linear_combination 95040*hw₇
    · rw [(normalized_fourth_power_actual_rows β (g 7)).1]
      simp only [g]
      linear_combination 11880*hw₈
    · exact power_root_inherited_derivative _ 4 3 ρ hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 4 2 ρ hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 4 1 ρ hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 4 0 ρ hqρ (by norm_num)
  refine ⟨fun i => g i.val,fun i => hrows i.val i.isLt,?_,?_,hρ,?_,?_,?_⟩
  · exact hf0
  · intro i hi
    fin_cases i <;> norm_num at hi <;> rfl
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt
  · simpa only [g,hf0,sub_zero,Nat.reduceSub] using northeast_chain_cost 12 g hre him

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
    ∃ (z : Fin 12 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[12 - (i.val + 1)] (q^4)).eval (z i) = 0) ∧
      z 0 = q.roots.sum / 3 ∧
      (∀ i : Fin 12, 8 ≤ i.val → z i = z 11) ∧ q.eval (z 11) = 0 ∧
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a * starRingEnd ℂ b).re = 0 ∧
      Monotone (fun i => (a * z i).re) ∧ Monotone (fun i => (b * z i).re) ∧
      chainCost z ≤ 4 * Real.sqrt 2 * R / 3 := by
  apply cubic_power_radius_of_strict_normalized_chain 4 (by norm_num) (11/2) 55
    (by norm_num) (by norm_num) 11 (by rfl) _ q hq hdeg o R hR hbound
  intro β hβR hβI
  obtain ⟨z,hroots,hstart,htail,_,hmR,hmI,_⟩ := normalized_fourth_chain_strict β hβR hβI
  refine ⟨z,?_,hstart,htail,hmR,hmI⟩
  intro i
  simpa only [Complex.ofReal_div,Complex.ofReal_ofNat,C_mul,C_ofNat] using hroots i
