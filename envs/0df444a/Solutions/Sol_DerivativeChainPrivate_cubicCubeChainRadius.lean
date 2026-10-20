-- Prove2me | solution 1 for DerivativeChainPrivate.cubicCubeChainRadius
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T14:41:39.872986+00:00
-- url     : https://prove2.me/submissions/da087d5e-fc6d-42e3-ae4f-74da79116f6c

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
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

theorem normalized_cubic_cube_expansion (β : ℂ) :
    (X^3-4*X-28*C β)^3 =
      C 1*X^9+C (-12)*X^7+C (-84*β)*X^6+C 48*X^5+C (672*β)*X^4+
      C (2352*β^2-64)*X^3+C (-1344*β)*X^2+C (-9408*β^2)*X^1+
      C (-21952*β^3)*X^0 := by
  simp only [C_sub,C_mul,C_pow,C_neg,C_ofNat]
  norm_num
  ring



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

theorem iterated_derivative_real_parent (p : Polynomial ℂ) (k : ℕ)
    (hk : k < p.natDegree) (w : ℂ)
    (hw : (Polynomial.derivative^[k] p).eval w = 0) :
    ∃ z : ℂ, p.eval z = 0 ∧ w.re ≤ z.re := by
  induction k generalizing p w with
  | zero => exact ⟨w, hw, le_rfl⟩
  | succ k ih =>
    have hkd : k < p.derivative.natDegree := by rw [Polynomial.natDegree_derivative]; omega
    rw [Function.iterate_succ_apply] at hw
    obtain ⟨u, hu, hwu⟩ := ih p.derivative hkd w hw
    obtain ⟨z, hz, huz⟩ := derivative_real_supporting_parent p (by omega) u hu
    exact ⟨z, hz, hwu.trans huz⟩

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

theorem fast_inverse_southeast_impossible (R x y r v α b A₀ A₁ : ℝ)
    (hR : 0 ≤ R) (hx : 0 < x) (hv : 0 ≤ v) (hxr : x ≤ r) (hvy : v ≤ y)
    (hWedge : 5/2 ≤ x^2-3*y^2) (hα : 3/5 < α) (hb : b < 1)
    (hA₀ : A₀ ≤ 1/40) (hA₁ : -(1/50) ≤ A₁)
    (hR₀ : R/x = (1/10)*(x^2-3*y^2)-7/25+A₀)
    (hR₁ : R/r = α*(r^2-3*v^2)-b+A₁) : False := by
  have hreal := div_le_div_of_nonneg_left hR hx hxr
  rw [hR₀,hR₁] at hreal
  have hsqx : x^2 ≤ r^2 := by nlinarith only [hx,hxr]
  have hsqy : v^2 ≤ y^2 := by nlinarith only [hv,hvy]
  have hdiff : 0 ≤ (r^2-3*v^2)-(x^2-3*y^2) := by linarith only [hsqx,hsqy]
  have hmul := mul_nonneg (show 0 ≤ α by linarith only [hα]) hdiff
  have hprod := mul_le_mul (show (1/2 : ℝ) ≤ α-1/10 by linarith only [hα]) hWedge
    (by norm_num : (0 : ℝ) ≤ 5/2) (show 0 ≤ α-1/10 by linarith only [hα])
  nlinarith only [hreal,hmul,hprod,hb,hA₀,hA₁]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem near_one_square_root_control (t s : ℂ) (hsq : s ^ 2 = t)
    (hs : 0 < s.re) (ht : ‖t - 1‖ ≤ 1 / 15) :
    ‖s - 1‖ ≤ 1 / 15 ∧ 9 / 10 ≤ s.re ∧
      3 ≤ ‖s + 1‖ ^ 2 ∧ ‖s + 1‖ ≤ 21 / 10 ∧
      2 / 5 ≤ ((s + 1)⁻¹).re ∧ ((s + 1)⁻¹).re ≤ 3 / 5 ∧ ‖(s + 1)⁻¹‖ ≤ 3 / 5 := by
  have hnorm : 1 ≤ ‖s + 1‖ := by
    have h := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hnormpos : 0 < ‖s + 1‖ := by linarith
  have hfactor : ‖s - 1‖ * ‖s + 1‖ = ‖t - 1‖ := by
    rw [← norm_mul]
    congr 1
    calc
      _ = s ^ 2 - 1 := by ring
      _ = t - 1 := by rw [hsq]
  have hclose : ‖s - 1‖ ≤ 1 / 15 :=
    (le_mul_of_one_le_right (norm_nonneg _) hnorm).trans (hfactor.le.trans ht)
  have hrep : 9 / 10 ≤ s.re := by
    have h := Complex.abs_re_le_norm (s - 1)
    simp only [Complex.sub_re, Complex.one_re] at h
    have hl := (abs_le.mp (h.trans hclose)).1
    linarith
  have hnormlower : 19 / 10 ≤ ‖s + 1‖ := by
    have h := Complex.re_le_norm (s + 1)
    simp only [Complex.add_re, Complex.one_re] at h
    linarith
  have hnormupper : ‖s + 1‖ ≤ 21 / 10 := by
    have h : ‖s + 1‖ ≤ ‖s - 1‖ + 2 := by
      convert! norm_add_le (s - 1) (2 : ℂ) using 1 <;> norm_num <;> ring
    linarith
  have hnorminv : ‖(s + 1)⁻¹‖ ≤ 3 / 5 := by
    rw [norm_inv]
    rw [inv_eq_one_div]
    apply (div_le_iff₀ hnormpos).2
    linarith
  have hrelower : 2 / 5 ≤ ((s + 1)⁻¹).re := by
    rw [Complex.inv_re, ← Complex.sq_norm]
    apply (le_div_iff₀ (sq_pos_of_pos hnormpos)).2
    simp only [Complex.add_re, Complex.one_re]
    nlinarith only [hnormupper, hnormpos, hrep]
  exact ⟨hclose, hrep, by nlinarith only [hnormlower, hnormpos],
    hnormupper, hrelower, (Complex.re_le_norm _).trans hnorminv, hnorminv⟩

theorem cube_radical_real_remainder_bounds (x y p D a b r : ℝ)
    (hx : 0 < x) (hy : y ≠ 0) (hU : 5 / 2 ≤ x ^ 2 + y ^ 2)
    (hp : 9 / 10 ≤ p) (hD : 3 ≤ D)
    (ha : 2 / 5 ≤ a) (ha' : a ≤ 3 / 5) (hab : a ^ 2 + b ^ 2 ≤ (3 / 5 : ℝ) ^ 2)
    (hr : 0 ≤ r) (hr' : r ≤ 3 / 2)
    (hkey : 6 * p * (x ^ 2 + y ^ 2) ^ 2 * D * b = x * y) :
    let U := x ^ 2 + y ^ 2
    let P := 16 * a + a ^ 2 - b ^ 2
    let Q := b * (16 + 2 * a)
    let A := r / (336 * U) * (P + (y / x) * Q)
    let B := r / (336 * U) * ((x / y) * Q - P)
    0 ≤ A ∧ A ≤ 1 / 50 ∧ -(1 / 50) ≤ B ∧ B ≤ 0 ∧
      0 ≤ (3 * A - B) / 2 ∧ (3 * A - B) / 2 ≤ 1 / 25 := by
  let U := x ^ 2 + y ^ 2
  have hUpos : 0 < U := by dsimp only [U]; linarith
  have hpD : 27 / 10 ≤ p * D := by
    have hmul := mul_nonneg (show 0 ≤ p - 9 / 10 by linarith) (show 0 ≤ D - 3 by linarith)
    nlinarith only [hmul, hp, hD]
  have hden : 40 * U ≤ 6 * p * U ^ 2 * D := by
    have hmul := mul_le_mul_of_nonneg_right hpD hUpos.le
    have hK : 40 ≤ 6 * p * U * D := by nlinarith only [hmul, hU]
    have hmul' := mul_le_mul_of_nonneg_right hK hUpos.le
    nlinarith only [hmul']
  have hdenpos : 0 < 6 * p * U ^ 2 * D := by nlinarith only [hden,hUpos]
  have hq₀ : (y / x) * b = y ^ 2 / (6 * p * U ^ 2 * D) := by
    apply (eq_div_iff hdenpos.ne').2
    calc
      _ = (y / x) * (6 * p * U ^ 2 * D * b) := by ring
      _ = (y / x) * (x * y) := by rw [hkey]
      _ = y ^ 2 := by field_simp
  have hq₁ : (x / y) * b = x ^ 2 / (6 * p * U ^ 2 * D) := by
    apply (eq_div_iff hdenpos.ne').2
    calc
      _ = (x / y) * (6 * p * U ^ 2 * D * b) := by ring
      _ = (x / y) * (x * y) := by rw [hkey]
      _ = x ^ 2 := by field_simp
  have hrat₀ : 0 ≤ (y / x) * b ∧ (y / x) * b ≤ 1 / 40 := by
    rw [hq₀]
    constructor
    · positivity
    · apply (div_le_iff₀ hdenpos).2
      dsimp only [U] at hden
      nlinarith only [hden, sq_nonneg x]
  have hrat₁ : 0 ≤ (x / y) * b ∧ (x / y) * b ≤ 1 / 40 := by
    rw [hq₁]
    constructor
    · positivity
    · apply (div_le_iff₀ hdenpos).2
      dsimp only [U] at hden
      nlinarith only [hden, sq_nonneg y]
  have hQ₀ : 0 ≤ (y / x) * (b * (16 + 2 * a)) ∧
      (y / x) * (b * (16 + 2 * a)) ≤ 1 / 2 := by
    rw [← mul_assoc]
    constructor
    · exact mul_nonneg hrat₀.1 (by linarith)
    · have h := mul_le_mul hrat₀.2 (show 16 + 2 * a ≤ 86 / 5 by linarith)
        (by linarith : 0 ≤ 16 + 2 * a) (by norm_num : (0 : ℝ) ≤ 1 / 40)
      linarith
  have hQ₁ : 0 ≤ (x / y) * (b * (16 + 2 * a)) ∧
      (x / y) * (b * (16 + 2 * a)) ≤ 1 / 2 := by
    rw [← mul_assoc]
    constructor
    · exact mul_nonneg hrat₁.1 (by linarith)
    · have h := mul_le_mul hrat₁.2 (show 16 + 2 * a ≤ 86 / 5 by linarith)
        (by linarith : 0 ≤ 16 + 2 * a) (by norm_num : (0 : ℝ) ≤ 1 / 40)
      linarith
  have hP : 6 ≤ 16 * a + a ^ 2 - b ^ 2 ∧ 16 * a + a ^ 2 - b ^ 2 ≤ 10 := by
    constructor <;> nlinarith only [ha,ha',hab,sq_nonneg a,sq_nonneg b]
  have hfac : 0 ≤ r / (336 * U) ∧ r / (336 * U) ≤ 1 / 560 := by
    constructor
    · positivity
    · apply (div_le_iff₀ (by positivity : 0 < 336 * U)).2
      dsimp only [U]
      linarith
  dsimp only
  change 0 ≤ r / (336 * U) * _ ∧ _
  have hA₀ : 0 ≤ r / (336 * U) * (16 * a + a ^ 2 - b ^ 2 + (y / x) * (b * (16 + 2 * a))) :=
    mul_nonneg hfac.1 (by linarith only [hP.1,hQ₀.1])
  have hA₁ : r / (336 * U) * (16 * a + a ^ 2 - b ^ 2 + (y / x) * (b * (16 + 2 * a))) ≤ 1 / 50 := by
    have h := mul_le_mul hfac.2 (show 16 * a + a ^ 2 - b ^ 2 +
      (y / x) * (b * (16 + 2 * a)) ≤ 21 / 2 by linarith only [hP.2,hQ₀.2])
      (by linarith only [hP.1,hQ₀.1] : 0 ≤ 16 * a + a ^ 2 - b ^ 2 + (y / x) * (b * (16 + 2 * a)))
      (by norm_num : (0 : ℝ) ≤ 1 / 560)
    linarith
  have hB₀ : -(1 / 50 : ℝ) ≤ r / (336 * U) * ((x / y) * (b * (16 + 2 * a)) -
      (16 * a + a ^ 2 - b ^ 2)) := by
    have h := mul_nonneg hfac.1 (show 0 ≤ (x / y) * (b * (16 + 2 * a)) -
      (16 * a + a ^ 2 - b ^ 2) + 10 by linarith only [hP.2,hQ₁.1])
    nlinarith only [h,hfac.2]
  have hB₁ : r / (336 * U) * ((x / y) * (b * (16 + 2 * a)) - (16 * a + a ^ 2 - b ^ 2)) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos hfac.1 (by linarith only [hQ₁.2,hP.1])
  exact ⟨hA₀,hA₁,hB₀,hB₁,by linarith only [hA₀,hB₁],by linarith only [hA₁,hB₀]⟩

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

theorem cube_radicand_close (z : ℂ) (hx : 5 / 2 ≤ z.re ^ 2) :
    ‖(1 + (1 / 6 : ℂ) / z ^ 2) - 1‖ ≤ 1 / 15 := by
  have hU : 5 / 2 ≤ ‖z‖ ^ 2 := by
    have h := Complex.sq_norm_sub_sq_re z
    nlinarith only [h,hx,sq_nonneg z.im]
  have hn : 0 < ‖z‖ ^ 2 := by linarith
  rw [add_sub_cancel_left, norm_div, norm_pow]
  norm_num
  apply (div_le_iff₀ hn).2
  linarith

theorem exists_positive_re_square_root (t : ℂ) (ht : 0 < t.re) :
    ∃ s : ℂ, s ^ 2 = t ∧ 0 < s.re := by
  obtain ⟨s,hs⟩ := IsAlgClosed.exists_pow_nat_eq t (show 0 < 2 by norm_num)
  have hsre : s.re ≠ 0 := by
    intro h
    have heq := congrArg Complex.re hs
    simp only [pow_two,Complex.mul_re,h,zero_mul,zero_sub] at heq
    nlinarith only [heq,ht,sq_nonneg s.im]
  rcases lt_or_gt_of_ne hsre with hn | hp
  · refine ⟨-s,?_,?_⟩
    · simpa only [neg_sq] using hs
    · simpa only [Complex.neg_re] using neg_pos.mpr hn
  · exact ⟨s,hs,hp⟩

theorem cube_radicand_positive_square_root (z : ℂ) (hx : 5 / 2 ≤ z.re ^ 2) :
    ∃ s : ℂ, s ^ 2 = 1 + (1 / 6 : ℂ) / z ^ 2 ∧ 0 < s.re := by
  apply exists_positive_re_square_root
  have hc := cube_radicand_close z hx
  have hr := Complex.abs_re_le_norm ((1 + (1 / 6 : ℂ) / z ^ 2) - 1)
  have hl := (abs_le.mp (hr.trans hc)).1
  simp only [Complex.sub_re,Complex.one_re] at hl
  linarith

theorem cube_radical_imaginary_relation (z s : ℂ) (hz : z ≠ 0)
    (hsq : s ^ 2 = 1 + (1 / 6 : ℂ) / z ^ 2) :
    6 * s.re * (z.re ^ 2 + z.im ^ 2) ^ 2 * ‖s + 1‖ ^ 2 * ((s + 1)⁻¹).im = z.re * z.im := by
  have hn : ‖z‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  have hIm := congrArg Complex.im hsq
  simp only [Complex.add_im,Complex.one_im,zero_add,Complex.div_im,
    ← Complex.sq_norm,norm_pow] at hIm
  norm_num [pow_two,Complex.mul_im,Complex.mul_re] at hIm
  have hsp : s + 1 ≠ 0 := by
    intro heq
    have hs : s = -1 := eq_neg_of_add_eq_zero_left heq
    rw [hs] at hsq
    norm_num at hsq
    exact hz (by simpa only [pow_eq_zero_iff (by norm_num : 2 ≠ 0)] using hsq)
  have hDn : ‖s + 1‖ ^ 2 ≠ 0 := pow_ne_zero 2 (norm_ne_zero_iff.mpr hsp)
  rw [Complex.inv_im, ← Complex.sq_norm]
  simp only [Complex.add_im,Complex.one_im,add_zero]
  have hprod : 6 * s.re * ‖z‖ ^ 4 * s.im = -(z.re * z.im) := by
    have hn4 : ‖z‖ ^ 4 ≠ 0 := pow_ne_zero 4 (norm_ne_zero_iff.mpr hz)
    field_simp at hIm
    nlinarith only [hIm]
  rw [Complex.sq_norm,Complex.normSq_apply] at hn
  have hzNorm : (z.re ^ 2 + z.im ^ 2) ^ 2 = ‖z‖ ^ 4 := by
    rw [show ‖z‖ ^ 4 = (‖z‖ ^ 2) ^ 2 by ring,Complex.sq_norm,Complex.normSq_apply]
    ring
  rw [hzNorm]
  field_simp [hDn]
  nlinarith only [hprod]

theorem cube_radical_remainder_bounds (z s : ℂ) (hx : 0 < z.re)
    (hy : z.im ≠ 0) (hX : 5 / 2 ≤ z.re ^ 2) (hs : 0 < s.re)
    (hsq : s ^ 2 = 1 + (1 / 6 : ℂ) / z ^ 2) :
    let T := (s + 1)⁻¹
    let E := ((Real.sqrt 2 / 336 : ℝ) : ℂ) * (16 * T + T ^ 2) / z
    0 ≤ E.re / z.re ∧ E.re / z.re ≤ 1 / 50 ∧
      -(1 / 50) ≤ E.im / z.im ∧ E.im / z.im ≤ 0 ∧
      0 ≤ (3 * (E.re / z.re) - E.im / z.im) / 2 ∧
      (3 * (E.re / z.re) - E.im / z.im) / 2 ≤ 1 / 25 := by
  let T := (s + 1)⁻¹
  let U := z.re ^ 2 + z.im ^ 2
  let E := ((Real.sqrt 2 / 336 : ℝ) : ℂ) * (16 * T + T ^ 2) / z
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hU : 5 / 2 ≤ U := by dsimp only [U]; nlinarith only [hX,sq_nonneg z.im]
  have hUpos : 0 < U := by linarith
  have hUnorm : ‖z‖ ^ 2 = U := by
    rw [Complex.sq_norm,Complex.normSq_apply]
    dsimp only [U]
    ring
  obtain ⟨_,hp,hD,_,ha,ha',htnorm⟩ := near_one_square_root_control _ s hsq hs
    (cube_radicand_close z hX)
  have hnormT := Complex.sq_norm T
  rw [Complex.normSq_apply] at hnormT
  have hab : T.re ^ 2 + T.im ^ 2 ≤ (3 / 5 : ℝ) ^ 2 := by
    nlinarith only [hnormT,htnorm,norm_nonneg T]
  have hrr : Real.sqrt 2 ≤ 3 / 2 := by
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num),Real.sqrt_nonneg 2]
  have hbound := cube_radical_real_remainder_bounds z.re z.im s.re (‖s + 1‖ ^ 2)
    T.re T.im (Real.sqrt 2) hx hy hU hp hD ha ha' hab (Real.sqrt_nonneg 2) hrr
    (cube_radical_imaginary_relation z s hz hsq)
  have hA : E.re / z.re = Real.sqrt 2 / (336 * U) *
      (16 * T.re + T.re ^ 2 - T.im ^ 2 + (z.im / z.re) * (T.im * (16 + 2 * T.re))) := by
    dsimp only [E]
    rw [Complex.div_re,←Complex.sq_norm,hUnorm]
    norm_num [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,pow_two]
    field_simp
    ring
  have hB : E.im / z.im = Real.sqrt 2 / (336 * U) *
      ((z.re / z.im) * (T.im * (16 + 2 * T.re)) - (16 * T.re + T.re ^ 2 - T.im ^ 2)) := by
    dsimp only [E]
    rw [Complex.div_im,←Complex.sq_norm,hUnorm]
    norm_num [Complex.mul_re,Complex.mul_im,Complex.add_re,Complex.add_im,pow_two]
    field_simp
    ring
  change 0 ≤ E.re / z.re ∧ _
  rw [hA,hB]
  exact hbound

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_cube_actual_row_values (β z : ℂ) :
    let p : Polynomial ℂ := (X ^ 3 - 4 * X - 28 * C β) ^ 3
    (derivative^[3] p).eval z = 504 *
      (z ^ 6 - 5 * z ^ 4 - 20 * β * z ^ 3 + 40/7 * z ^ 2 + 32 * β * z - 16/21 + 28 * β ^ 2) ∧
    (derivative^[4] p).eval z = 3024 *
      (z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + 40/21 * z + 16/3 * β) ∧
    (derivative^[5] p).eval z = 15120 * (z ^ 4 - 2 * z ^ 2 - 4 * β * z + 8/21) ∧
    (derivative^[6] p).eval z = 60480 * (z ^ 3 - z - β) ∧
    (derivative^[7] p).eval z = 60480 * (3 * z ^ 2 - 1) ∧
    (derivative^[8] p).eval z = 362880 * z := by
  let p : Polynomial ℂ := (X ^ 3 - 4 * X - 28 * C β) ^ 3
  have hexpand := normalized_cubic_cube_expansion β
  change p = _ at hexpand
  have heval (k : ℕ) : (derivative^[k] p).eval z =
      (9 : ℕ).descFactorial k * z ^ (9-k) - 12 * (7 : ℕ).descFactorial k * z ^ (7-k) -
      84 * β * (6 : ℕ).descFactorial k * z ^ (6-k) +
      48 * (5 : ℕ).descFactorial k * z ^ (5-k) +
      672 * β * (4 : ℕ).descFactorial k * z ^ (4-k) +
      (2352 * β ^ 2 - 64) * (3 : ℕ).descFactorial k * z ^ (3-k) -
      1344 * β * (2 : ℕ).descFactorial k * z ^ (2-k) -
      9408 * β ^ 2 * (1 : ℕ).descFactorial k * z ^ (1-k) -
      21952 * β ^ 3 * (0 : ℕ).descFactorial k * z ^ (0-k) := by
    rw [hexpand]
    simp only [iterate_map_add derivative k,iterate_derivative_C_mul,
      iterate_derivative_X_pow_eq_C_mul,eval_add,eval_mul,eval_C,eval_pow,eval_X]
    ring
  dsimp only
  refine ⟨?_,?_,?_,?_,?_,?_⟩ <;> change (derivative^[_] p).eval z = _
  all_goals rw [heval]; norm_num [Nat.descFactorial] <;> ring

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_cube_quartic_step (β w : ℂ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hw : w ^ 3 - w = β) (hwpos : 0 < w.re) :
    ∃ z : ℂ,
      z ^ 4 - 2 * z ^ 2 - 4 * β * z + 8 / 21 = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 7 / 4 ≤ z.re ^ 2 ∧
      β / z = (1/4 : ℂ) * z ^ 2 - 1/2 + (2/21 : ℂ) / z ^ 2 := by
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
  let p : Polynomial ℂ := X ^ 4 - 2 * X ^ 2 - 4 * C β * X + C (8 / 21)
  have hpdeg : p.natDegree = 4 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w = 0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 4 * hw
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx1 : 1 ≤ z.re := hw1.trans hxz
  have hx : 0 < z.re := by linarith
  have hz0 : z ≠ 0 := by intro h; simp [h] at hx
  have hzroot : z ^ 4 - 2 * z ^ 2 - 4 * β * z + 8 / 21 = 0 := by
    simpa only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] using hz
  have hzinv : β / z = (1 / 4 : ℂ) * z ^ 2 - 1 / 2 + (2 / 21 : ℂ) / (z ^ 2 - 0) := by
    have hform : β / z = (z ^ 4 - 2 * z ^ 2 + 8/21) / (4 * z ^ 2) := by
      apply (div_eq_div_iff hz0 (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz0))).2
      linear_combination (-z) * hzroot
    rw [hform]
    field_simp
    ring
  obtain ⟨hzR,hzI,hzphase,hD⟩ := rational_inverse_parts β z (1/4) (1/2) (2/21) 0 hz0
    (by simpa using pow_ne_zero 2 hz0) (by push_cast; exact hzinv)
  simp only [Complex.ofReal_zero,sub_zero,zero_mul,mul_zero,add_zero] at hzR hzI hzphase hD
  let U := z.re ^ 2 + z.im ^ 2
  have hU : 1 ≤ U := by dsimp only [U]; nlinarith only [hx1,sq_nonneg z.im]
  have hUpos : 0 < U := by linarith
  have hDpos : 0 < ‖z ^ 2‖ ^ 2 := by rw [hD]; change 0 < U ^ 2; positivity
  have hD1 : 1 ≤ ‖z ^ 2‖ ^ 2 := by rw [hD]; change 1 ≤ U ^ 2; nlinarith only [hU]
  have hphasepos : 0 < (1/4 : ℝ) - (2/21) / ‖z ^ 2‖ ^ 2 := by
    have hquot : (2/21 : ℝ) / ‖z ^ 2‖ ^ 2 ≤ 2/21 :=
      (div_le_iff₀ hDpos).mpr (by linarith)
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
        ((2/21) * U / ‖z ^ 2‖ ^ 2) 0 (-((2/21) * U / ‖z ^ 2‖ ^ 2)) 0
        β.re β.im w.re w.im z.re z.im
        (by norm_num) (by norm_num) hwpos hv hxz hlt.le hR hI
        (by norm_num) (by
          have hA : 0 ≤ (2/21 : ℝ) * U / ‖z ^ 2‖ ^ 2 := by positivity
          linarith only [hA]) (by norm_num)
      · rw [hwR]; field_simp <;> ring
      · rw [hwI]; field_simp <;> ring
      · rw [hzR]; dsimp only [U]; field_simp <;> ring
      · rw [hzI]; dsimp only [U]; field_simp <;> ring
  have hXpos : 0 < z.re ^ 2 := sq_pos_of_pos hx
  have hbr : 0 ≤ (1/4 : ℝ) * (z.re ^ 2 - 3 * z.im ^ 2) - 1/2 +
      (2/21) * U / ‖z ^ 2‖ ^ 2 := by
    apply nonneg_of_mul_nonneg_right ?_ hx
    simpa only [U] using (hzR ▸ hR)
  have hrewrite : (2/21 : ℝ) * U / ‖z ^ 2‖ ^ 2 = (2/21) / U := by
    rw [hD]; change (2/21 : ℝ) * U / U ^ 2 = (2/21) / U
    field_simp
  rw [hrewrite] at hbr
  have hquot := div_le_div_of_nonneg_left (show (0 : ℝ) ≤ 2/21 by norm_num) hXpos
    (show z.re ^ 2 ≤ U by dsimp only [U]; nlinarith only [sq_nonneg z.im])
  have hweak : 0 ≤ z.re ^ 2 / 4 - 1/2 + (2/21) / z.re ^ 2 := by
    nlinarith only [hbr,hquot,sq_nonneg z.im]
  have hid : z.re ^ 2 / 4 - 1/2 + (2/21) / z.re ^ 2 =
      ((z.re ^ 2) ^ 2 - 2 * z.re ^ 2 + 8/21) / (4 * z.re ^ 2) := by field_simp; ring
  rw [hid] at hweak
  have hpoly := (le_div_iff₀ (show 0 < 4 * z.re ^ 2 by positivity)).mp hweak
  have hX1 : 1 ≤ z.re ^ 2 := by nlinarith only [hx1]
  have hX : 7/4 ≤ z.re ^ 2 := by
    by_contra hfail
    have hprod := mul_nonneg (show 0 ≤ z.re ^ 2 - 1 by linarith)
      (show 0 ≤ 7/4 - z.re ^ 2 by linarith)
    nlinarith only [hpoly,hprod,lt_of_not_ge hfail]
  exact ⟨z,hzroot,hxz,himorder,hX,by simpa only [sub_zero] using hzinv⟩

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_cube_quintic_step (β w : ℂ)
    (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) (hwpos : 0 < w.re) (hwim : 0 ≤ w.im)
    (hwX : 7/4 ≤ w.re ^ 2)
    (hwroot : w ^ 4 - 2 * w ^ 2 - 4 * β * w + 8/21 = 0)
    (hwinv : β / w = (1/4 : ℂ) * w ^ 2 - 1/2 + (2/21 : ℂ) / w ^ 2) :
    ∃ z : ℂ,
      z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + 40/21 * z + 16/3 * β = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 5/2 ≤ z.re ^ 2 ∧
      β / z = (1/10 : ℂ) * z ^ 2 - 7/25 + (36/875 : ℂ) / (z ^ 2 - 8/15) := by
  have hwne : w ≠ 0 := by intro h; simp [h] at hwpos
  obtain ⟨hwR,hwI,hwphase,hwD⟩ := rational_inverse_parts β w (1/4) (1/2) (2/21) 0 hwne
    (by simpa using pow_ne_zero 2 hwne) (by push_cast; simpa using hwinv)
  simp only [Complex.ofReal_zero,sub_zero,zero_mul,mul_zero,add_zero] at hwR hwI hwphase hwD
  let W := w.re ^ 2 + w.im ^ 2
  have hW : 1 ≤ W := by dsimp only [W]; nlinarith only [hwX,sq_nonneg w.im]
  have hWpos : 0 < W := by linarith
  have hwD1 : 1 ≤ ‖w ^ 2‖ ^ 2 := by rw [hwD]; change 1 ≤ W ^ 2; nlinarith only [hW]
  have hwDp : 0 < ‖w ^ 2‖ ^ 2 := by linarith
  have hwphasep : 0 < (1/4 : ℝ) - (2/21) / ‖w ^ 2‖ ^ 2 := by
    have hquot : (2/21 : ℝ) / ‖w ^ 2‖ ^ 2 ≤ 2/21 :=
      (div_le_iff₀ hwDp).mpr (by linarith)
    linarith
  have hwzero := (quadrant_phase_forces_nonnegative_im β w _ hR hI hwpos hwphasep hwphase).2
  let p : Polynomial ℂ := X ^ 5 - C (10/3) * X ^ 3 - 10 * C β * X ^ 2 +
    C (40/21) * X + C (16/3) * C β
  have hpdeg : p.natDegree = 5 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w = 0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 5 * hwroot
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hXpre : 7/4 ≤ z.re ^ 2 := by nlinarith only [hwX,hxz,hwpos]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hx
  have hpole : z ^ 2 - (8/15 : ℂ) ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    have hi := congrArg Complex.im h
    norm_num [pow_two,Complex.mul_re,Complex.mul_im] at hr hi
    have hm : z.re * z.im = 0 := by nlinarith only [hi]
    have hy := (mul_eq_zero.mp hm).resolve_left hx.ne'
    rw [hy] at hr
    nlinarith only [hr,hXpre]
  have hzroot : z ^ 5 - 10/3 * z ^ 3 - 10 * β * z ^ 2 + 40/21 * z + 16/3 * β = 0 := by
    simpa only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] using hz
  have hzinv : β / z = (1/10 : ℂ) * z ^ 2 - 7/25 + (36/875 : ℂ) / (z ^ 2 - 8/15) := by
    have hform : β / z = (z ^ 4 - 10/3 * z ^ 2 + 40/21) / (10 * (z ^ 2 - 8/15)) := by
      apply (div_eq_div_iff hz0 (mul_ne_zero (by norm_num) hpole)).2
      linear_combination -hzroot
    rw [hform]
    apply (div_eq_iff (mul_ne_zero (by norm_num : (10 : ℂ) ≠ 0) hpole)).2
    calc
      _ = ((1/10 : ℂ) * z ^ 2 - 7/25) * (10 * (z ^ 2 - 8/15)) + (36/875) * 10 := by ring
      _ = ((1/10 : ℂ) * z ^ 2 - 7/25) * (10 * (z ^ 2 - 8/15)) +
          ((36/875) / (z ^ 2 - 8/15) * (z ^ 2 - 8/15)) * 10 := by rw [div_mul_cancel₀ _ hpole]
      _ = _ := by ring
  obtain ⟨hzR,hzI,hzphase,hD⟩ := rational_inverse_parts β z (1/10) (7/25) (36/875) (8/15)
    hz0 (by push_cast; exact hpole) (by push_cast; exact hzinv)
  push_cast at hzR hzI hzphase hD
  let U := z.re ^ 2 + z.im ^ 2
  let D := ‖z ^ 2 - (8/15 : ℂ)‖ ^ 2
  have hU : 7/4 ≤ U := by dsimp only [U]; nlinarith only [hXpre,sq_nonneg z.im]
  have hUc : 1 ≤ U - 8/15 := by linarith
  have hUcp : 0 < U - 8/15 := by linarith
  have hDlow : (U - 8/15) ^ 2 ≤ D := by
    dsimp only [U,D]
    nlinarith only [hD,sq_nonneg z.im]
  have hD1 : 1 ≤ D := by nlinarith only [hDlow,hUc]
  have hDp : 0 < D := by linarith
  have hphasep : 0 < (1/10 : ℝ) - (36/875) / D := by
    have hquot : (36/875 : ℝ) / D ≤ 36/875 := (div_le_iff₀ hDp).mpr (by linarith)
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
      have hCw : (3 * ((2/21) * W / ‖w ^ 2‖ ^ 2) - (-((2/21) * W / ‖w ^ 2‖ ^ 2))) / 2 ≤ 4/21 := by
        have hid : (3 * ((2/21) * W / ‖w ^ 2‖ ^ 2) - (-((2/21) * W / ‖w ^ 2‖ ^ 2))) / 2 =
            (4/21 : ℝ) / W := by rw [hwD]; change _ = (4/21 : ℝ) / W; field_simp; ring
        rw [hid]
        apply (div_le_iff₀ hWpos).2
        linarith
      have hAz : 0 ≤ (36/875 : ℝ) * (U - 8/15) / D := by positivity
      have hBz : 0 ≤ (36/875 : ℝ) * (U + 8/15) / D := by positivity
      apply inverse_graph_southeast_impossible (1/4) (1/10) (1/2) (7/25)
        ((2/21) * W / ‖w ^ 2‖ ^ 2) ((36/875) * (U-8/15) / D)
        (-((2/21) * W / ‖w ^ 2‖ ^ 2)) (-((36/875) * (U+8/15) / D)) (4/21)
        β.re β.im w.re w.im z.re z.im
        (by norm_num) (by norm_num) hwpos hv hxz hlt.le hR hI hCw
        (by linarith only [hAz,hBz]) (by norm_num)
      · rw [hwR]; dsimp only [W]; field_simp <;> ring
      · rw [hwI]; dsimp only [W]; field_simp <;> ring
      · rw [hzR]; dsimp only [U,D]; field_simp <;> ring
      · rw [hzI]; dsimp only [U,D]; field_simp <;> ring
  have hXcp : 0 < z.re ^ 2 - 8/15 := by linarith
  have hA : (36/875 : ℝ) * (U - 8/15) / D ≤ (36/875) / (z.re ^ 2 - 8/15) := by
    calc
      _ ≤ (36/875) / (U-8/15) := by
        apply (div_le_div_iff₀ hDp hUcp).2
        nlinarith only [mul_le_mul_of_nonneg_left hDlow (show (0 : ℝ) ≤ 36/875 by norm_num)]
      _ ≤ _ := div_le_div_of_nonneg_left (by norm_num) hXcp
        (by dsimp only [U]; nlinarith only [sq_nonneg z.im])
  have hbr : 0 ≤ (1/10 : ℝ) * (z.re ^ 2 - 3 * z.im ^ 2) - 7/25 + (36/875) * (U-8/15) / D := by
    apply nonneg_of_mul_nonneg_right ?_ hx
    simpa only [U,D] using (hzR ▸ hR)
  have hweak : 0 ≤ z.re ^ 2 - 14/5 + (72/175) / (z.re ^ 2 - 8/15) := by
    have hcoeff : (72/175 : ℝ) / (z.re ^ 2 - 8/15) =
        10 * ((36/875) / (z.re ^ 2 - 8/15)) := by ring
    rw [hcoeff]
    nlinarith only [hbr,hA,sq_nonneg z.im]
  have hid : z.re ^ 2 - 14/5 + (72/175) / (z.re ^ 2 - 8/15) =
      ((z.re ^ 2) ^ 2 - 10/3 * z.re ^ 2 + 40/21) / (z.re ^ 2 - 8/15) := by
    apply (eq_div_iff hXcp.ne').2
    calc
      _ = (z.re ^ 2 - 14/5) * (z.re ^ 2 - 8/15) +
          ((72/175) / (z.re ^ 2 - 8/15)) * (z.re ^ 2 - 8/15) := by ring
      _ = (z.re ^ 2 - 14/5) * (z.re ^ 2 - 8/15) + 72/175 := by rw [div_mul_cancel₀ _ hXcp.ne']
      _ = _ := by ring
  rw [hid] at hweak
  have hpoly := (le_div_iff₀ hXcp).mp hweak
  have hX : 5/2 ≤ z.re ^ 2 := by
    by_contra hfail
    have hprod := mul_nonneg (show 0 ≤ z.re ^ 2 - 7/4 by linarith)
      (show 0 ≤ 5/2 - z.re ^ 2 by linarith)
    nlinarith only [hpoly,hprod,lt_of_not_ge hfail]
  exact ⟨z,hzroot,hxz,himorder,hX,hzinv⟩

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cube_quintic_pole_bounds (U D : ℝ) (hU : 5/2 ≤ U)
    (hD : (U - 8/15) ^ 2 ≤ D) :
    0 < D ∧ 0 ≤ (36/875) * (U-8/15) / D ∧
      (36/875) * (U-8/15) / D ≤ 1/40 ∧
      0 ≤ (36/875) * (2*U-8/15) / D ∧
      (36/875) * (2*U-8/15) / D ≤ 1/12 := by
  have hV : 0 < U - 8/15 := by linarith
  have hDp : 0 < D := lt_of_lt_of_le (sq_pos_of_pos hV) hD
  refine ⟨hDp,?_,?_,?_,?_⟩
  · exact div_nonneg (mul_nonneg (by norm_num) hV.le) hDp.le
  · apply (div_le_iff₀ hDp).2
    have hprod := mul_nonneg hV.le (show 0 ≤ U-8/15-40*(36/875) by linarith)
    nlinarith only [hD,hprod]
  · exact div_nonneg (mul_nonneg (by norm_num) (by linarith)) hDp.le
  · apply (div_le_iff₀ hDp).2
    have hprod := mul_nonneg (show 0 ≤ U-8/15-3/2 by linarith)
      (show 0 ≤ U-8/15+3/10 by linarith)
    nlinarith only [hD,hprod,hU]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cube_sextic_algebraic_gaps :
    let r := Real.sqrt 2
    let αm := (5 - 3*r)/14
    let αp := (5 + 3*r)/14
    let bm := (32 - 15*r)/56
    let bp := (32 + 15*r)/56
    1/28 < αm ∧ αm < 1/10 ∧ 3/5 < αp ∧ bp < 1 ∧
      1/25 < bm - 1/7 ∧ 1/12 < 7/25 - bm ∧ 0 < bp - 1/7 := by
  have hs := Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)
  have hn := Real.sqrt_nonneg 2
  have hlo : 7/5 < Real.sqrt 2 := by nlinarith only [hs,hn]
  have hhi : Real.sqrt 2 < 29/20 := by nlinarith only [hs,hn]
  dsimp only
  exact ⟨by linarith,by linarith,by linarith,by linarith,
    by linarith,by linarith,by linarith⟩

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cube_radical_inverse_identity (z s r : ℂ) (hz : z ≠ 0) (hs : s + 1 ≠ 0)
    (hsq : s ^ 2 = 1 + (1/6 : ℂ) / z ^ 2) :
    (10*z^2-16-6*r*(z^2-4/3)*s)/28 =
      (5-3*r)/14*z^2-(32-15*r)/56 +
        (((r/336)*(16*(s+1)⁻¹+((s+1)⁻¹)^2)/z)/z) := by
  have hprod : 6 * z ^ 2 * (s-1) * (s+1) = 1 := by
    field_simp at hsq
    linear_combination hsq
  have hfirst : z ^ 2 * (s-1) = 1 / (6*(s+1)) := by
    apply (eq_div_iff (mul_ne_zero (by norm_num) hs)).2
    linear_combination hprod
  have hdiff : s-1 = 1/(6*z^2*(s+1)) := by
    apply (eq_div_iff (mul_ne_zero (mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)) hs)).2
    linear_combination hprod
  have hG : (10*z^2-16-6*r*(z^2-4/3)*s)/28 - (5-3*r)/14*z^2 + (32-15*r)/56 =
      (r/56)*(s-1)*(16+1/(s+1)) := by
    calc
      _ = (3*r/14)*(-z^2*(s-1)+(4/3)*s-5/4) := by ring
      _ = (3*r/14)*(-1/(6*(s+1))+(4/3)*s-5/4) := by rw [neg_mul,hfirst]; ring
      _ = _ := by field_simp; ring
  calc
    _ = (5-3*r)/14*z^2-(32-15*r)/56+(r/56)*(s-1)*(16+1/(s+1)) := by
      linear_combination hG
    _ = _ := by rw [hdiff]; field_simp; ring

theorem cube_sextic_inverse_split (β z s r : ℂ) (hz : z ≠ 0) (hr : r ^ 2 = 2)
    (hsq : s ^ 2 = 1 + (1/6 : ℂ) / z ^ 2)
    (hroot : z ^ 6 - 5*z^4 - 20*β*z^3 + 40/7*z^2 + 32*β*z - 16/21 + 28*β^2 = 0) :
    β / z = (10*z^2-16-6*r*(z^2-4/3)*s)/28 ∨
      β / z = (10*z^2-16+6*r*(z^2-4/3)*s)/28 := by
  have hint : 21*z^6-105*z^4-420*β*z^3+120*z^2+672*β*z-16+588*β^2 = 0 := by
    linear_combination 21*hroot
  have hid : (3*z^2)*((28*(β/z)-(10*z^2-16))^2-
      72*(z^2-4/3)^2*(1+(1/6 : ℂ)/z^2)) =
      4*(21*z^6-105*z^4-420*β*z^3+120*z^2+672*β*z-16+588*β^2) := by
    field_simp
    ring
  have hdisc : (28*(β/z)-(10*z^2-16))^2-
      72*(z^2-4/3)^2*(1+(1/6 : ℂ)/z^2) = 0 := by
    apply (mul_eq_zero.mp (show (3*z^2)*_ = 0 by rw [hid,hint,mul_zero])).resolve_left
    exact mul_ne_zero (by norm_num) (pow_ne_zero 2 hz)
  have hB : (6*r*(z^2-4/3)*s)^2 = 72*(z^2-4/3)^2*(1+(1/6 : ℂ)/z^2) := by
    calc
      _ = 36*r^2*(z^2-4/3)^2*s^2 := by ring
      _ = _ := by rw [hr,hsq]; ring
  have hfactor : (28*(β/z)-(10*z^2-16)-6*r*(z^2-4/3)*s) *
      (28*(β/z)-(10*z^2-16)+6*r*(z^2-4/3)*s) = 0 := by
    calc
      _ = (28*(β/z)-(10*z^2-16))^2-(6*r*(z^2-4/3)*s)^2 := by ring
      _ = 0 := by rw [hB]; exact hdisc
  rcases mul_eq_zero.mp hfactor with hplus | hminus
  · right
    linear_combination (1/28 : ℂ)*hplus
  · left
    linear_combination (1/28 : ℂ)*hminus

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

theorem quotient_imaginary_identity (z e : ℂ) (hx : z.re ≠ 0) (hy : z.im ≠ 0) :
    (e/z).im/(2*z.re*z.im) = (e.im/z.im-e.re/z.re)/(2*(z.re^2+z.im^2)) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hD : Complex.normSq z ≠ 0 := by
    rw [← Complex.sq_norm]
    exact pow_ne_zero 2 (norm_ne_zero_iff.mpr hz)
  rw [Complex.div_im]
  simp only [Complex.normSq_apply]
  have hsum : z.re*z.re+z.im*z.im ≠ 0 := by simpa only [Complex.normSq_apply] using hD
  field_simp

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cube_radical_quotient_imaginary_bounds (z s : ℂ) (hx : 0 < z.re)
    (hy : z.im ≠ 0) (hX : 5/2 ≤ z.re^2) (hs : 0 < s.re)
    (hsq : s^2 = 1+(1/6 : ℂ)/z^2) :
    let T := (s+1)⁻¹
    let E := ((Real.sqrt 2/336 : ℝ) : ℂ)*(16*T+T^2)/z;
    -(1/125) ≤ (E/z).im/(2*z.re*z.im) ∧ (E/z).im/(2*z.re*z.im) ≤ 0 := by
  obtain ⟨hA,hA',hB,hB',_,_⟩ := cube_radical_remainder_bounds z s hx hy hX hs hsq
  dsimp only
  rw [quotient_imaginary_identity z _ hx.ne' hy]
  have hU : 5/2 ≤ z.re^2+z.im^2 := by nlinarith only [hX,sq_nonneg z.im]
  have hUp : 0 < 2*(z.re^2+z.im^2) := by linarith
  constructor
  · apply (le_div_iff₀ hUp).2
    linarith only [hA',hB,hU]
  · exact div_nonpos_of_nonpos_of_nonneg (by linarith only [hA,hB']) hUp.le

theorem cube_radical_graph_phase (β z s : ℂ) (α b σ : ℝ)
    (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2) (hs : 0 < s.re)
    (hsq : s^2 = 1+(1/6 : ℂ)/z^2) (hα : 1/125 < α)
    (hσ : σ = 1 ∨ σ = -1) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hβ : β/z = (α : ℂ)*z^2-(b : ℂ)+
      (σ : ℂ)*(((Real.sqrt 2/336 : ℝ) : ℂ)*(16*(s+1)⁻¹+((s+1)⁻¹)^2)/z)/z) :
    0 ≤ z.im ∧ (β.im = 0 → z.im = 0) := by
  by_cases hy : z.im = 0
  · exact ⟨hy.ge,fun _ => hy⟩
  let E := ((Real.sqrt 2/336 : ℝ) : ℂ)*(16*(s+1)⁻¹+((s+1)⁻¹)^2)/z
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  obtain ⟨hlo,hhi⟩ := cube_radical_quotient_imaginary_bounds z s hx hy hX hs hsq
  have hk : 0 < α+σ*((E/z).im/(2*z.re*z.im)) := by
    rcases hσ with h | h <;> rw [h] <;> dsimp only [E] <;> linarith
  obtain ⟨_,_,hphase⟩ := cubic_graph_coordinate_parts β z ((σ : ℂ)*E) α b hz hβ
  have hscaled : (((σ : ℂ)*E)/z).im = σ*(E/z).im := by
    rw [mul_div_assoc,Complex.mul_im]
    simp only [Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
  rw [hscaled] at hphase
  apply quadrant_phase_forces_nonnegative_im β z _ hR hI hx hk
  rw [hphase]
  field_simp

theorem cube_radical_real_on_real (z s : ℂ) (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2)
    (hy : z.im = 0) (hs : 0 < s.re) (hsq : s^2 = 1+(1/6 : ℂ)/z^2) :
    (((Real.sqrt 2/336 : ℝ) : ℂ)*(16*(s+1)⁻¹+((s+1)⁻¹)^2)/z).im = 0 := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  obtain ⟨_,_,hD,_,_,_,_⟩ := near_one_square_root_control _ s hsq hs (cube_radicand_close z hX)
  have hDp : 0 < ‖s+1‖^2 := by linarith
  have hkey := cube_radical_imaginary_relation z s hz hsq
  rw [hy,mul_zero] at hkey
  have hTim : ((s+1)⁻¹).im = 0 :=
    (mul_eq_zero.mp hkey).resolve_left (ne_of_gt (by positivity))
  norm_num [Complex.div_im,Complex.mul_im,Complex.mul_re,Complex.add_im,Complex.add_re,
    hTim,hy,pow_two]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem cube_quintic_inverse_estimates (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2)
    (hβ : β/z = (1/10 : ℂ)*z^2-7/25+(36/875 : ℂ)/(z^2-8/15)) :
    let U := z.re^2+z.im^2
    let D := ‖z^2-(8/15 : ℂ)‖^2
    let A := (36/875)* (U-8/15)/D
    let B := -(36/875)* (U+8/15)/D
    β.re = z.re*((1/10)*(z.re^2-3*z.im^2)-7/25+A) ∧
      β.im = z.im*((1/10)*(3*z.re^2-z.im^2)-7/25+B) ∧
      0 ≤ A ∧ A ≤ 1/40 ∧ 0 ≤ (3*A-B)/2 ∧ (3*A-B)/2 ≤ 1/12 ∧
      5/2 ≤ z.re^2-3*z.im^2 ∧ 0 ≤ z.im ∧ (β.im = 0 → z.im = 0) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  have hpole : z^2-(8/15 : ℂ) ≠ 0 := by
    intro h
    have hn := congrArg norm (sub_eq_zero.mp h)
    norm_num [norm_pow,norm_div] at hn
    nlinarith only [hn,hX,Complex.sq_norm_sub_sq_re z,sq_nonneg z.im]
  obtain ⟨hRe,hIm,hphase,hD⟩ := rational_inverse_parts β z (1/10) (7/25) (36/875) (8/15)
    hz (by push_cast; exact hpole) (by push_cast; exact hβ)
  push_cast at hRe hIm hphase hD
  let U := z.re^2+z.im^2
  let D := ‖z^2-(8/15 : ℂ)‖^2
  let A := (36/875)* (U-8/15)/D
  let B := -(36/875)* (U+8/15)/D
  have hU : 5/2 ≤ U := by dsimp only [U]; nlinarith only [hX,sq_nonneg z.im]
  have hDlow : (U-8/15)^2 ≤ D := by dsimp only [U,D]; nlinarith only [hD,sq_nonneg z.im]
  obtain ⟨hDp,hA0,hA1,hC0,hC1⟩ := cube_quintic_pole_bounds U D hU hDlow
  have hCeq : (3*A-B)/2 = (36/875)*(2*U-8/15)/D := by dsimp only [A,B]; ring
  have hbr : 0 ≤ (1/10)*(z.re^2-3*z.im^2)-7/25+A := by
    apply nonneg_of_mul_nonneg_right ?_ hx
    simpa only [A,U,D] using (hRe ▸ hR)
  have hWedge : 5/2 ≤ z.re^2-3*z.im^2 := by linarith only [hbr,hA1]
  have hD1 : 1 ≤ D := by nlinarith only [hDlow,hU]
  have hk : 0 < (1/10 : ℝ)-(36/875)/D := by
    have hquot : (36/875 : ℝ)/D ≤ 36/875 := (div_le_iff₀ hDp).mpr (by linarith)
    linarith
  obtain ⟨hzim,hzero⟩ := quadrant_phase_forces_nonnegative_im β z _ hR hI hx hk hphase
  change _ ∧ _ ∧ 0 ≤ A ∧ A ≤ 1/40 ∧ 0 ≤ (3*A-B)/2 ∧ (3*A-B)/2 ≤ 1/12 ∧ _
  refine ⟨hRe,?_,hA0,hA1,?_,?_,hWedge,hzim,hzero⟩
  · simpa only [B,U,D,neg_mul,neg_div,sub_eq_add_neg] using hIm
  · rw [hCeq]; exact hC0
  · rw [hCeq]; exact hC1

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate

theorem cube_sextic_inverse_estimates (β z : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hx : 0 < z.re) (hX : 5/2 ≤ z.re^2)
    (hroot : z^6-5*z^4-20*β*z^3+40/7*z^2+32*β*z-16/21+28*β^2 = 0) :
    ∃ (α b : ℝ) (e : ℂ),
      1/28 < α ∧ 1/25 < b-1/7 ∧ β/z = (α : ℂ)*z^2-(b : ℂ)+e/z ∧
      0 ≤ z.im ∧ (β.im = 0 → z.im = 0) ∧ (z.im = 0 → β.im = 0) ∧
      (z.im ≠ 0 → (3*(e.re/z.re)-e.im/z.im)/2 ≤ 1/25) ∧
      ((α < 1/10 ∧ 1/12 < 7/25-b ∧ (z.im ≠ 0 → 0 ≤ (3*(e.re/z.re)-e.im/z.im)/2)) ∨
        (3/5 < α ∧ b < 1 ∧ (z.im ≠ 0 → -(1/50) ≤ e.re/z.re))) := by
  have hz : z ≠ 0 := by intro h; simp [h] at hx
  obtain ⟨s,hsq,hs⟩ := cube_radicand_positive_square_root z hX
  have hsp : s+1 ≠ 0 := by
    intro h
    have hr := congrArg Complex.re h
    simp only [Complex.add_re,Complex.one_re,Complex.zero_re] at hr
    linarith
  let αm := (5-3*Real.sqrt 2)/14
  let αp := (5+3*Real.sqrt 2)/14
  let bm := (32-15*Real.sqrt 2)/56
  let bp := (32+15*Real.sqrt 2)/56
  let E := ((Real.sqrt 2/336 : ℝ) : ℂ)*(16*(s+1)⁻¹+((s+1)⁻¹)^2)/z
  obtain ⟨hαm,hαm',hαp,hbp,hbm,hbm',_⟩ := cube_sextic_algebraic_gaps
  have hbpgap : 1/25 < bp-1/7 := by dsimp only [bp]; linarith [Real.sqrt_nonneg 2]
  have hr : (Real.sqrt 2 : ℂ)^2 = 2 := by
    rw [← Complex.ofReal_pow,Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num)]
    norm_num
  have hminus : (10*z^2-16-6*(Real.sqrt 2 : ℂ)*(z^2-4/3)*s)/28 =
      (αm : ℂ)*z^2-(bm : ℂ)+E/z := by
    convert! cube_radical_inverse_identity z s (Real.sqrt 2 : ℂ) hz hsp hsq using 1 <;>
      try dsimp only [αm,bm,E] <;> push_cast <;> ring
  have hplus : (10*z^2-16+6*(Real.sqrt 2 : ℂ)*(z^2-4/3)*s)/28 =
      (αp : ℂ)*z^2-(bp : ℂ)+(-E)/z := by
    calc
      _ = (5/7 : ℂ)*z^2-8/7-(10*z^2-16-6*(Real.sqrt 2 : ℂ)*(z^2-4/3)*s)/28 := by ring
      _ = _ := by rw [hminus]; dsimp only [αm,bm,αp,bp]; push_cast; ring
  obtain ⟨α,b,σ,hα,hb,hσ,hgraph,hcases⟩ : ∃ (α b σ : ℝ),
      1/28 < α ∧ 1/25 < b-1/7 ∧ (σ = 1 ∨ σ = -1) ∧
      β/z = (α : ℂ)*z^2-(b : ℂ)+(σ : ℂ)*E/z ∧
      ((σ = 1 ∧ α < 1/10 ∧ 1/12 < 7/25-b) ∨ (σ = -1 ∧ 3/5 < α ∧ b < 1)) := by
    rcases cube_sextic_inverse_split β z s (Real.sqrt 2 : ℂ) hz hr hsq hroot with hm | hp
    · rw [hminus] at hm
      exact ⟨αm,bm,1,hαm,hbm,Or.inl rfl,by simpa using hm,Or.inl ⟨rfl,hαm',hbm'⟩⟩
    · rw [hplus] at hp
      exact ⟨αp,bp,-1,by dsimp only [αp]; linarith only [hαp],hbpgap,Or.inr rfl,
        by simpa using hp,Or.inr ⟨rfl,hαp,hbp⟩⟩
  let e := (σ : ℂ)*E
  have hphase := cube_radical_graph_phase β z s α b σ hx hX hs hsq (by linarith) hσ hR hI hgraph
  obtain ⟨_,hImag,_⟩ := cubic_graph_coordinate_parts β z e α b hz hgraph
  have hAre : e.re/z.re = σ*(E.re/z.re) := by
    dsimp only [e]
    simp only [Complex.mul_re,Complex.ofReal_re,Complex.ofReal_im,zero_mul,sub_zero]
    ring
  have hBim : e.im/z.im = σ*(E.im/z.im) := by
    dsimp only [e]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,zero_mul,add_zero]
    ring
  have hC : (3*(e.re/z.re)-e.im/z.im)/2 = σ*((3*(E.re/z.re)-E.im/z.im)/2) := by
    rw [hAre,hBim]
    ring
  refine ⟨α,b,e,hα,hb,hgraph,hphase.1,hphase.2,?_,?_,?_⟩
  · intro hy
    have hE : E.im = 0 := cube_radical_real_on_real z s hx hX hy hs hsq
    rw [hImag,hy,zero_mul,zero_add]
    dsimp only [e]
    simp only [Complex.mul_im,Complex.ofReal_re,Complex.ofReal_im,hE,mul_zero,zero_mul,add_zero]
  · intro hy
    obtain ⟨_,_,_,_,hlo,hhi⟩ := cube_radical_remainder_bounds z s hx hy hX hs hsq
    change 0 ≤ (3*(E.re/z.re)-E.im/z.im)/2 at hlo
    change (3*(E.re/z.re)-E.im/z.im)/2 ≤ 1/25 at hhi
    rw [hC]
    rcases hσ with h | h <;> rw [h] <;> linarith only [hlo,hhi]
  · rcases hcases with ⟨hσ₁,hα₁,hb₁⟩ | ⟨hσ₁,hα₁,hb₁⟩
    · left
      refine ⟨hα₁,hb₁,?_⟩
      intro hy
      obtain ⟨_,_,_,_,hlo,_⟩ := cube_radical_remainder_bounds z s hx hy hX hs hsq
      rw [hC,hσ₁,one_mul]
      exact hlo
    · right
      refine ⟨hα₁,hb₁,?_⟩
      intro hy
      obtain ⟨_,hhi,_,_,_,_⟩ := cube_radical_remainder_bounds z s hx hy hX hs hsq
      change E.re/z.re ≤ 1/50 at hhi
      rw [hAre,hσ₁,neg_one_mul]
      linarith only [hhi]

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_cube_sextic_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwX : 5/2 ≤ w.re^2)
    (hwroot : w^5-10/3*w^3-10*β*w^2+40/21*w+16/3*β = 0)
    (hwinv : β/w = (1/10 : ℂ)*w^2-7/25+(36/875 : ℂ)/(w^2-8/15)) :
    ∃ z : ℂ, z^6-5*z^4-20*β*z^3+40/7*z^2+32*β*z-16/21+28*β^2 = 0 ∧
      w.re ≤ z.re ∧ w.im ≤ z.im ∧ 5/2 ≤ z.re^2 ∧ 0 ≤ z.im ∧
      ∃ (α b : ℝ) (e : ℂ), 1/28 < α ∧ 1/25 < b-1/7 ∧
        β/z = (α : ℂ)*z^2-(b : ℂ)+e/z ∧ (β.im = 0 → z.im = 0) ∧
        (z.im ≠ 0 → (3*(e.re/z.re)-e.im/z.im)/2 ≤ 1/25) := by
  let W := w.re^2+w.im^2
  let Dw := ‖w^2-(8/15 : ℂ)‖^2
  let Aw := (36/875)*(W-8/15)/Dw
  let Bw := -(36/875)*(W+8/15)/Dw
  obtain ⟨hwR,hwI,_,hAw,_,hCw,hWedge,_,hwzero⟩ :=
    cube_quintic_inverse_estimates β w hR hI hwpos hwX hwinv
  let p : Polynomial ℂ := X^6-5*X^4-20*C β*X^3+C (40/7)*X^2+32*C β*X-C (16/21)+28*(C β)^2
  have hpdeg : p.natDegree = 6 := by dsimp only [p]; compute_degree <;> norm_num
  have hcritical : p.derivative.eval w = 0 := by
    norm_num [p,derivative_mul,derivative_sub,derivative_add,derivative_pow,derivative_X,
      eval_sub,eval_mul,eval_add,eval_pow,eval_X,eval_C,C_ofNat]
    linear_combination 6*hwroot
  obtain ⟨z,hz,hxz⟩ := derivative_real_supporting_parent p (by rw [hpdeg]; norm_num) w hcritical
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hX : 5/2 ≤ z.re^2 := by nlinarith only [hwX,hxz,hwpos]
  have hz0 : z ≠ 0 := by intro h; simp [h] at hx
  have hzroot : z^6-5*z^4-20*β*z^3+40/7*z^2+32*β*z-16/21+28*β^2 = 0 := by
    simpa only [p,eval_sub,eval_add,eval_pow,eval_X,eval_mul,eval_ofNat,eval_C] using hz
  obtain ⟨α,b,e,hα,hb,hgraph,hzim,hzero,hreal,hC,hcases⟩ :=
    cube_sextic_inverse_estimates β z hR hI hx hX hzroot
  obtain ⟨hzR,hzI,_⟩ := cubic_graph_coordinate_parts β z e α b hz0 hgraph
  let Az := e.re/z.re
  let Bz := e.im/z.im
  have himorder : w.im ≤ z.im := by
    by_contra hfail
    have hlt : z.im < w.im := lt_of_not_ge hfail
    by_cases hzIm : z.im = 0
    · have hwIm := hwzero (hreal hzIm)
      linarith
    · have hv : 0 < z.im := lt_of_le_of_ne hzim (Ne.symm hzIm)
      have hy : 0 < w.im := lt_trans hv hlt
      have hR₀ : β.re/w.re = (1/10)*(w.re^2-3*w.im^2)-7/25+Aw := by
        rw [hwR]; dsimp only [Aw,W,Dw]; field_simp <;> ring
      have hI₀ : β.im/w.im = (1/10)*(3*w.re^2-w.im^2)-7/25+Bw := by
        rw [hwI]; dsimp only [Bw,W,Dw]; field_simp <;> ring
      have hR₁ : β.re/z.re = α*(z.re^2-3*z.im^2)-b+Az := by
        rw [hzR]; dsimp only [Az]; field_simp <;> ring
      have hI₁ : β.im/z.im = α*(3*z.re^2-z.im^2)-b+Bz := by
        rw [hzI]; dsimp only [Bz]; field_simp <;> ring
      rcases hcases with ⟨hslow,hgap,hCnonneg⟩ | ⟨hfast,hbup,hAlower⟩
      · exact inverse_graph_southeast_impossible (1/10) α (7/25) b Aw Az Bw Bz (1/12)
          β.re β.im w.re w.im z.re z.im (by linarith only [hα]) hslow hwpos hv hxz hlt.le hR hI
          hCw (hCnonneg hzIm) hgap hR₀ hI₀ hR₁ hI₁
      · exact fast_inverse_southeast_impossible β.re w.re w.im z.re z.im α b Aw Az
          hR hwpos hv.le hxz hlt.le hWedge hfast hbup hAw (hAlower hzIm) hR₀ hR₁
  exact ⟨z,hzroot,hxz,himorder,hX,hzim,α,b,e,hα,hb,hgraph,hzero,hC⟩

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_cube_source_step (β w : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im)
    (hwpos : 0 < w.re) (hwim : 0 ≤ w.im)
    (hwroot : w^6-5*w^4-20*β*w^3+40/7*w^2+32*β*w-16/21+28*β^2 = 0)
    (α b : ℝ) (e : ℂ) (hα : 1/28 < α) (hb : 1/25 < b-1/7)
    (hgraph : β/w = (α : ℂ)*w^2-(b : ℂ)+e/w)
    (hwzero : β.im = 0 → w.im = 0)
    (hC : w.im ≠ 0 → (3*(e.re/w.re)-e.im/w.im)/2 ≤ 1/25) :
    ∃ z : ℂ, z^3-4*z-28*β = 0 ∧ w.re ≤ z.re ∧ w.im ≤ z.im ∧ 0 < z.re := by
  let q : Polynomial ℂ := X^3-4*X-28*C β
  let p := q^3
  have hpdeg : p.natDegree = 9 := by dsimp only [p,q]; compute_degree <;> norm_num
  have hactual : (derivative^[3] p).eval w = 0 := by
    have h := (normalized_cube_actual_row_values β w).1
    rw [hwroot,mul_zero] at h
    exact h
  obtain ⟨z,hz,hxz⟩ := iterated_derivative_real_parent p 3 (by rw [hpdeg]; norm_num) w hactual
  have hx : 0 < z.re := lt_of_lt_of_le hwpos hxz
  have hz0 : z ≠ 0 := by intro h; simp [h] at hx
  have hw0 : w ≠ 0 := by intro h; simp [h] at hwpos
  have hzq : q.eval z = 0 := by
    have hpow : (q.eval z)^3 = 0 := by simpa only [p,eval_pow] using hz
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hpow
  have hzroot : z^3-4*z-28*β = 0 := by
    simpa only [q,eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat] using hzq
  have hzinv : β/z = (1/28 : ℂ)*z^2-1/7+0/(z^2-0) := by
    simp only [zero_div,add_zero]
    apply (div_eq_iff hz0).2
    linear_combination (-1/28 : ℂ)*hzroot
  obtain ⟨hzR,hzI,hzphase,_⟩ := rational_inverse_parts β z (1/28) (1/7) 0 0 hz0
    (by simpa using pow_ne_zero 2 hz0) (by push_cast; exact hzinv)
  simp only [Complex.ofReal_zero,sub_zero,zero_mul,mul_zero,zero_div,add_zero] at hzR hzI hzphase
  obtain ⟨hzim,_⟩ := quadrant_phase_forces_nonnegative_im β z (1/28) hR hI hx (by norm_num) hzphase
  obtain ⟨hwR,hwI,_⟩ := cubic_graph_coordinate_parts β w e α b hw0 hgraph
  have himorder : w.im ≤ z.im := by
    by_contra hfail
    have hlt : z.im < w.im := lt_of_not_ge hfail
    by_cases hzIm : z.im = 0
    · have hβzero : β.im = 0 := by rw [hzI,hzIm,zero_mul]
      have hwIm := hwzero hβzero
      linarith
    · have hv : 0 < z.im := lt_of_le_of_ne hzim (Ne.symm hzIm)
      have hy : 0 < w.im := lt_trans hv hlt
      apply inverse_graph_southeast_impossible α (1/28) b (1/7)
        (e.re/w.re) 0 (e.im/w.im) 0 (1/25)
        β.re β.im w.re w.im z.re z.im
        (by norm_num) hα hwpos hv hxz hlt.le hR hI (hC hy.ne') (by norm_num) hb
      · rw [hwR]; field_simp <;> ring
      · rw [hwI]; field_simp <;> ring
      · rw [hzR]; field_simp <;> ring
      · rw [hzI]; field_simp <;> ring
  exact ⟨z,hzroot,hxz,himorder,hx⟩

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem normalized_cubic_cube_chain (β : ℂ) (hR : 0 ≤ β.re) (hI : 0 ≤ β.im) :
    ∃ z : Fin 9 → ℂ,
      (∀ i, (derivative^[9-(i.val+1)] ((X^3-4*X-28*C β)^3)).eval (z i) = 0) ∧
      z 0 = 0 ∧ z 6 = z 7 ∧ z 7 = z 8 ∧
      (z 8)^3-4*z 8-28*β = 0 ∧ 0 < (z 8).re ∧
      Monotone (fun i => (z i).re) ∧ Monotone (fun i => (z i).im) ∧
      chainCost z ≤ Real.sqrt 2 * ‖z 8‖ := by
  obtain ⟨w₃,hw₃,_⟩ := normalized_cubic_quadrant_root β hR hI
  obtain ⟨hw₃re,hw₃im,_⟩ := normalized_cubic_positive_root_sector β w₃ hR hI hw₃.1 hw₃.2
  obtain ⟨w₄,hw₄,h₃₄r,h₃₄i,hw₄X,hw₄inv⟩ := normalized_cube_quartic_step β w₃ hR hI hw₃.1 hw₃.2
  have hw₄pos : 0 < w₄.re := lt_of_lt_of_le hw₃.2 h₃₄r
  obtain ⟨w₅,hw₅,h₄₅r,h₄₅i,hw₅X,hw₅inv⟩ := normalized_cube_quintic_step β w₄ hR hI
    hw₄pos (hw₃im.trans h₃₄i) hw₄X hw₄ hw₄inv
  have hw₅pos : 0 < w₅.re := lt_of_lt_of_le hw₄pos h₄₅r
  obtain ⟨w₆,hw₆,h₅₆r,h₅₆i,_,hw₆im,α,b,e,hα,hb,hw₆inv,hw₆zero,hw₆C⟩ :=
    normalized_cube_sextic_step β w₅ hR hI hw₅pos hw₅X hw₅ hw₅inv
  have hw₆pos : 0 < w₆.re := lt_of_lt_of_le hw₅pos h₅₆r
  obtain ⟨ρ,hρ,h₆ρr,h₆ρi,hρpos⟩ := normalized_cube_source_step β w₆ hR hI hw₆pos
    hw₆im hw₆ α b e hα hb hw₆inv hw₆zero hw₆C
  let c : ℝ := Real.sqrt 3 / 3
  have hcpos : 0 < c := div_pos (Real.sqrt_pos.mpr (by norm_num)) (by norm_num)
  have hc2 : c^2 = 1/3 := by
    dsimp only [c]
    nlinarith only [Real.sq_sqrt (show (0 : ℝ) ≤ 3 by norm_num)]
  have hc1 : c ≤ 1 := by nlinarith only [hc2,hcpos]
  have hcc : (c : ℂ)^2 = 1/3 := by
    rw [←Complex.ofReal_pow,hc2,Complex.ofReal_div]
    norm_num
  let g : ℕ → ℂ
    | 0 => 0
    | 1 => (c : ℂ)
    | 2 => w₃
    | 3 => w₄
    | 4 => w₅
    | 5 => w₆
    | _ => ρ
  have hre : ∀ i < 8, (g i).re ≤ (g (i+1)).re := by
    intro i hi
    interval_cases i <;> norm_num [g] <;>
      linarith only [hcpos,hc1,hw₃re,h₃₄r,h₄₅r,h₅₆r,h₆ρr]
  have him : ∀ i < 8, (g i).im ≤ (g (i+1)).im := by
    intro i hi
    interval_cases i <;> norm_num [g] <;>
      linarith only [hw₃im,h₃₄i,h₄₅i,h₅₆i,h₆ρi]
  have hqρ : (X^3-4*X-28*C β : Polynomial ℂ).eval ρ = 0 := by
    simpa only [eval_sub,eval_mul,eval_pow,eval_X,eval_C,eval_ofNat] using hρ
  have hrows (i : ℕ) (hi : i < 9) :
      (derivative^[9-(i+1)] ((X^3-4*X-28*C β)^3)).eval (g i) = 0 := by
    interval_cases i
    · rw [(normalized_cube_actual_row_values β (g 0)).2.2.2.2.2]
      simp only [g,mul_zero]
    · rw [(normalized_cube_actual_row_values β (g 1)).2.2.2.2.1]
      simp only [g,hcc]
      norm_num
    · rw [(normalized_cube_actual_row_values β (g 2)).2.2.2.1]
      simp only [g,hw₃.1,sub_self,mul_zero]
    · rw [(normalized_cube_actual_row_values β (g 3)).2.2.1]
      simp only [g,hw₄,mul_zero]
    · rw [(normalized_cube_actual_row_values β (g 4)).2.1]
      simp only [g,hw₅,mul_zero]
    · rw [(normalized_cube_actual_row_values β (g 5)).1]
      simp only [g,hw₆,mul_zero]
    · exact power_root_inherited_derivative _ 3 2 ρ hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 3 1 ρ hqρ (by norm_num)
    · exact power_root_inherited_derivative _ 3 0 ρ hqρ (by norm_num)
  refine ⟨fun i => g i.val,fun i => hrows i.val i.isLt,rfl,rfl,rfl,hρ,hρpos,?_,?_,?_⟩
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact hre i.val i.isLt
  · apply Fin.monotone_iff_le_succ.mpr
    intro i
    exact him i.val i.isLt
  · simpa only [g,sub_zero,Nat.reduceSub] using northeast_chain_cost 9 g hre him

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

theorem normalized_cubic_cube_frame (β : ℂ) (hR : 0 ≤ β.re) :
    ∃ (z : Fin 9 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[9-(i.val+1)] ((X^3-4*X-28*C β)^3)).eval (z i) = 0) ∧
      z 0 = 0 ∧ z 6 = z 7 ∧ z 7 = z 8 ∧
      (z 8)^3-4*z 8-28*β = 0 ∧ 0 < (z 8).re ∧
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a*starRingEnd ℂ b).re = 0 ∧
      Monotone (fun i => (a*z i).re) ∧ Monotone (fun i => (b*z i).re) ∧
      chainCost z ≤ Real.sqrt 2*‖z 8‖ := by
  by_cases hI : 0 ≤ β.im
  · obtain ⟨z,hroot,hstart,htail₀,htail₁,hend,hpos,hre,him,hcost⟩ := normalized_cubic_cube_chain β hR hI
    refine ⟨z,1,-Complex.I,hroot,hstart,htail₀,htail₁,hend,hpos,by simp,by simp,by simp,?_,?_,hcost⟩
    · simpa only [one_mul] using hre
    · simpa [Complex.mul_re] using him
  · let γ := starRingEnd ℂ β
    have hγR : 0 ≤ γ.re := by simpa only [γ,Complex.conj_re] using hR
    have hγI : 0 ≤ γ.im := by dsimp only [γ]; rw [Complex.conj_im]; linarith
    obtain ⟨z,hroot,hstart,htail₀,htail₁,hend,hpos,hre,him,hcost⟩ := normalized_cubic_cube_chain γ hγR hγI
    let f : Fin 9 → ℂ := fun i => starRingEnd ℂ (z i)
    have hmap : ((X^3-4*X-28*C γ)^3 : Polynomial ℂ).map (starRingEnd ℂ) =
        (X^3-4*X-28*C β)^3 := by simp [γ]
    have hroots (i : Fin 9) :
        (derivative^[9-(i.val+1)] ((X^3-4*X-28*C β)^3)).eval (f i) = 0 := by
      rw [←hmap,conjugate_derivative_eval,hroot,map_zero]
    refine ⟨f,1,Complex.I,hroots,?_,?_,?_,?_,?_,by simp,by simp,by simp,?_,?_,?_⟩
    · simpa only [f,hstart,map_zero]
    · exact congrArg (starRingEnd ℂ) htail₀
    · exact congrArg (starRingEnd ℂ) htail₁
    · have h := congrArg (starRingEnd ℂ) hend
      simpa [γ,f,Complex.conj_ofNat] using h
    · simpa only [f,Complex.conj_re] using hpos
    · simpa only [f,one_mul,Complex.conj_re] using hre
    · simpa [f,Complex.mul_re] using him
    · simpa only [f,chainCost_conjugate,Complex.norm_conj] using hcost

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem cubic_triple_normalization (u v w : ℂ)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0) :
    ∃ c β : ℂ, c ≠ 0 ∧ 0 ≤ β.re ∧
      ((X-C u)*(X-C v)*(X-C w)).comp (C ((u+v+w)/3)+C c*X) =
        C (c^3)*(X^3-4*X-28*C β) := by
  let η := (u+v+w)/3
  let A := (u^2+v^2+w^2-u*v-u*w-v*w)/3
  let B := (u-η)*(v-η)*(w-η)
  have hdepress (t : ℂ) : (η+t-u)*(η+t-v)*(η+t-w) = t^3-A*t-B := by
    dsimp only [η,A,B]
    ring
  obtain ⟨c,hc2⟩ := IsAlgClosed.exists_pow_nat_eq (A/4) (show 0 < 2 by norm_num)
  have hc : c ≠ 0 := by
    intro h
    apply hA
    change A = 0
    rw [h] at hc2
    linear_combination (-4 : ℂ)*hc2
  have hcomp (c : ℂ) (hc : c ≠ 0) (hc2 : c^2 = A/4) :
      ((X-C u)*(X-C v)*(X-C w)).comp (C η+C c*X) =
        C (c^3)*(X^3-4*X-28*C (B/(28*c^3))) := by
    have hAc : A = 4*c^2 := by linear_combination (-4 : ℂ)*hc2
    apply Polynomial.funext
    intro z
    simp only [eval_comp,eval_mul,eval_C,eval_add,eval_X,eval_sub,eval_pow,eval_ofNat]
    rw [hdepress (c*z),hAc]
    field_simp
  by_cases hβ : 0 ≤ (B/(28*c^3)).re
  · exact ⟨c,B/(28*c^3),hc,hβ,hcomp c hc hc2⟩
  · have hc' : -c ≠ 0 := neg_ne_zero.mpr hc
    have hc2' : (-c)^2 = A/4 := by simpa only [neg_sq] using hc2
    have hneg : B/(28*(-c)^3) = -(B/(28*c^3)) := by
      rw [show (-c)^3 = -(c^3) by ring,mul_neg,div_neg]
    refine ⟨-c,B/(28*(-c)^3),hc',?_,hcomp (-c) hc' hc2'⟩
    rw [hneg,Complex.neg_re]
    linarith

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial

theorem cubic_triple_nonzero_moment_chain (u v w o : ℂ) (R : ℝ) (_hR : 0 ≤ R)
    (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0) :
    let q := (X-C u)*(X-C v)*(X-C w)
    ∃ (z : Fin 9 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[9-(i.val+1)] (q^3)).eval (z i) = 0) ∧
      z 0 = (u+v+w)/3 ∧ z 6 = z 7 ∧ z 7 = z 8 ∧ q.eval (z 8) = 0 ∧
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a*starRingEnd ℂ b).re = 0 ∧
      Monotone (fun i => (a*z i).re) ∧ Monotone (fun i => (b*z i).re) ∧
      chainCost z ≤ 4*Real.sqrt 2*R/3 := by
  let q : Polynomial ℂ := (X-C u)*(X-C v)*(X-C w)
  let η := (u+v+w)/3
  obtain ⟨c,β,hc,hβ,hcomp⟩ := cubic_triple_normalization u v w hA
  obtain ⟨g,a,b,hroots,hstart,htail₀,htail₁,_,_,ha,hb,hab,hmonoA,hmonoB,hcost⟩ :=
    normalized_cubic_cube_frame β hβ
  let f : Fin 9 → ℂ := fun i => η+c*g i
  have hcube : (q^3).comp (C η+C c*X) = C (c^9)*(X^3-4*X-28*C β)^3 := by
    rw [pow_comp,hcomp,mul_pow,←C_pow,←pow_mul]
  have hfroot (i : Fin 9) : (derivative^[9-(i.val+1)] (q^3)).eval (f i) = 0 :=
    affine_derivative_root (q^3) ((X^3-4*X-28*C β)^3) η c (c^9) hc hcube _ (g i) (hroots i)
  have hqend : q.eval (f 8) = 0 := by
    have h := hfroot 8
    change (q^3).eval (f 8) = 0 at h
    have hpow : (q.eval (f 8))^3 = 0 := by simpa only [eval_pow] using h
    exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hpow
  have hcenter : ‖f 8-η‖ ≤ 4*R/3 := by
    have h := hqend
    simp only [q,eval_mul,eval_sub,eval_X,eval_C] at h
    rcases mul_eq_zero.mp h with huv | hw'
    · rcases mul_eq_zero.mp huv with hu' | hv'
      · rw [sub_eq_zero.mp hu']
        exact cubic_root_centroid_radius u v w o R hu hv hw
      · rw [sub_eq_zero.mp hv']
        have hη : (v+u+w)/3 = η := by dsimp only [η]; ring
        simpa only [hη] using cubic_root_centroid_radius v u w o R hv hu hw
    · rw [sub_eq_zero.mp hw']
      have hη : (w+u+v)/3 = η := by dsimp only [η]; ring
      simpa only [hη] using cubic_root_centroid_radius w u v o R hw hu hv
  have hfcost : chainCost f ≤ 4*Real.sqrt 2*R/3 := by
    rw [chainCost_affine]
    calc
      _ ≤ ‖c‖*(Real.sqrt 2*‖g 8‖) := mul_le_mul_of_nonneg_left hcost (norm_nonneg c)
      _ = Real.sqrt 2*‖f 8-η‖ := by dsimp only [f]; rw [add_sub_cancel_left,norm_mul]; ring
      _ ≤ Real.sqrt 2*(4*R/3) := mul_le_mul_of_nonneg_left hcenter (Real.sqrt_nonneg 2)
      _ = _ := by ring
  obtain ⟨A,B,hAunit,hBunit,horth,hmono₀,hmono₁⟩ :=
    affine_orthonormal_coordinates g a b η c hc ha hb hab hmonoA hmonoB
  refine ⟨f,A,B,hfroot,?_,?_,?_,hqend,hAunit,hBunit,horth,hmono₀,hmono₁,hfcost⟩
  · simp only [f,hstart,mul_zero,add_zero,η]
  · exact congrArg (fun z => η+c*z) htail₀
  · exact congrArg (fun z => η+c*z) htail₁

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
open Filter Topology
namespace DerivativeChainPrivate

theorem framed_cube_chain_collision_limit (p : ℕ → Polynomial ℂ) (q : Polynomial ℂ)
    (hp : ∀ j, (p j).natDegree ≤ 9) (hq : q.natDegree ≤ 9)
    (hc : ∀ k, Tendsto (fun j => (p j).coeff k) atTop (𝓝 (q.coeff k)))
    (z : ℕ → Fin 9 → ℂ) (a b : ℕ → ℂ) (M : ℝ) (hM : 0 ≤ M)
    (hbound : ∀ j i, ‖z j i‖ ≤ M)
    (hroot : ∀ j i, (Polynomial.derivative^[9-(i.val+1)] (p j)).eval (z j i) = 0)
    (η : ℂ) (hstart : ∀ j, z j 0 = η)
    (htail₀ : ∀ j, z j 6 = z j 7) (htail₁ : ∀ j, z j 7 = z j 8)
    (ha : ∀ j, ‖a j‖ = 1) (hb : ∀ j, ‖b j‖ = 1)
    (hab : ∀ j, (a j*starRingEnd ℂ (b j)).re = 0)
    (hmonoA : ∀ j, Monotone (fun i => (a j*z j i).re))
    (hmonoB : ∀ j, Monotone (fun i => (b j*z j i).re))
    (c : ℕ → ℝ) (C : ℝ) (hcLim : Tendsto c atTop (𝓝 C))
    (hcost : ∀ j, chainCost (z j) ≤ c j) :
    ∃ (w : Fin 9 → ℂ) (A B : ℂ),
      (∀ i, (Polynomial.derivative^[9-(i.val+1)] q).eval (w i) = 0) ∧
      w 0 = η ∧ w 6 = w 7 ∧ w 7 = w 8 ∧
      ‖A‖ = 1 ∧ ‖B‖ = 1 ∧ (A*starRingEnd ℂ B).re = 0 ∧
      Monotone (fun i => (A*w i).re) ∧ Monotone (fun i => (B*w i).re) ∧ chainCost w ≤ C := by
  let packed (j : ℕ) : ((Fin 9 → ℂ) × ℂ) × ℂ := ((z j,a j),b j)
  let S := max M 1
  have hS : 0 ≤ S := le_trans (by norm_num) (le_max_right M 1)
  have hmem (j : ℕ) : packed j ∈ Metric.closedBall 0 S := by
    rw [Metric.mem_closedBall,dist_zero_right]
    change max (max ‖z j‖ ‖a j‖) ‖b j‖ ≤ S
    have hzNorm : ‖z j‖ ≤ M := (pi_norm_le_iff_of_nonneg hM).mpr (hbound j)
    exact max_le (max_le (hzNorm.trans (le_max_left M 1))
      (by rw [ha]; exact le_max_right M 1)) (by rw [hb]; exact le_max_right M 1)
  obtain ⟨u,_,φ,hφ,hlim⟩ := (isCompact_closedBall (0 : ((Fin 9 → ℂ) × ℂ) × ℂ) S).isSeqCompact hmem
  let w := u.1.1
  let A := u.1.2
  let B := u.2
  have hφlim := hφ.tendsto_atTop
  have hzlim : Tendsto (fun j => z (φ j)) atTop (𝓝 w) := by
    have hc : Continuous (fun p : ((Fin 9 → ℂ) × ℂ) × ℂ => p.1.1) := continuous_fst.fst
    simpa only [Function.comp_def,packed,w] using hc.continuousAt.tendsto.comp hlim
  have hAlim : Tendsto (fun j => a (φ j)) atTop (𝓝 A) := by
    have hc : Continuous (fun p : ((Fin 9 → ℂ) × ℂ) × ℂ => p.1.2) := continuous_fst.snd
    simpa only [Function.comp_def,packed,A] using hc.continuousAt.tendsto.comp hlim
  have hBlim : Tendsto (fun j => b (φ j)) atTop (𝓝 B) := by
    have hc : Continuous (fun p : ((Fin 9 → ℂ) × ℂ) × ℂ => p.2) := continuous_snd
    simpa only [Function.comp_def,packed,B] using hc.continuousAt.tendsto.comp hlim
  have hcoord (i : Fin 9) : Tendsto (fun j => z (φ j) i) atTop (𝓝 (w i)) :=
    (continuous_apply i).continuousAt.tendsto.comp hzlim
  refine ⟨w,A,B,?_,?_,?_,?_,?_,?_,?_,?_,?_,?_⟩
  · intro i
    have hrootlim := iterate_derivative_eval_tendsto (fun j => p (φ j)) q 9
      (fun j => hp (φ j)) hq (fun k => (hc k).comp hφlim)
      (9-(i.val+1)) (fun j => z (φ j) i) (w i) (hcoord i)
    exact tendsto_nhds_unique hrootlim (by
      simpa only [hroot] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => (0 : ℂ)) atTop (𝓝 0)))
  · exact tendsto_nhds_unique (hcoord 0) (by
      simpa only [hstart] using
        (tendsto_const_nhds : Tendsto (fun _ : ℕ => η) atTop (𝓝 η)))
  · have h := hcoord 6
    have heq : (fun j => z (φ j) 6) = (fun j => z (φ j) 7) := funext (fun j => htail₀ (φ j))
    rw [heq] at h
    exact tendsto_nhds_unique h (hcoord 7)
  · have h := hcoord 7
    have heq : (fun j => z (φ j) 7) = (fun j => z (φ j) 8) := funext (fun j => htail₁ (φ j))
    rw [heq] at h
    exact tendsto_nhds_unique h (hcoord 8)
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
  · have hcontinuous : Continuous (fun v : Fin 9 → ℂ => chainCost v) := by
      unfold chainCost
      fun_prop
    exact le_of_tendsto_of_tendsto (hcontinuous.continuousAt.tendsto.comp hzlim)
      (hcLim.comp hφlim) (Eventually.of_forall (fun j => hcost (φ j)))

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

theorem triple_cube_natDegree (u v w : ℂ) :
    (((X-C u)*(X-C v)*(X-C w))^3 : Polynomial ℂ).natDegree = 9 := by
  compute_degree <;> norm_num

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

theorem cubic_triple_zero_moment_chain (u v w o : ℂ) (R : ℝ) (hR : 0 ≤ R)
    (hu : ‖u-o‖ ≤ R) (hv : ‖v-o‖ ≤ R) (hw : ‖w-o‖ ≤ R)
    (hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 = 0) :
    let q := (X-C u)*(X-C v)*(X-C w)
    ∃ (z : Fin 9 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[9-(i.val+1)] (q^3)).eval (z i) = 0) ∧
      z 0 = (u+v+w)/3 ∧ z 6 = z 7 ∧ z 7 = z 8 ∧ q.eval (z 8) = 0 ∧
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a*starRingEnd ℂ b).re = 0 ∧
      Monotone (fun i => (a*z i).re) ∧ Monotone (fun i => (b*z i).re) ∧
      chainCost z ≤ 4*Real.sqrt 2*R/3 := by
  classical
  let q : Polynomial ℂ := (X-C u)*(X-C v)*(X-C w)
  let η := (u+v+w)/3
  let d := u-η
  by_cases hd : d = 0
  · obtain ⟨hUV,hVW⟩ := cubic_zero_moment_centered_root u v w hA hd
    subst v
    subst w
    let f : Fin 9 → ℂ := fun _ => u
    have hpower : q^3 = (X-C u)^9 := by dsimp only [q]; ring
    refine ⟨f,1,-Complex.I,?_,?_,rfl,rfl,?_,by simp,by simp,by simp,?_,?_,?_⟩
    · intro i
      change (derivative^[9-(i.val+1)] (q^3)).eval u = 0
      rw [hpower]
      exact power_root_inherited_derivative (X-C u) 9 _ u (by simp) (by omega)
    · change u = (u+u+u)/3
      ring
    · simp [q,f]
    · intro i j hij
      exact le_rfl
    · intro i j hij
      exact le_rfl
    · have hc : chainCost f = 0 := by simp [f,chainCost]
      rw [hc]
      positivity
  · let ε : ℕ → ℝ := fun j => (1/2)^j
    have hεpos (j : ℕ) : 0 < ε j := pow_pos (by norm_num) j
    have hεone (j : ℕ) : ε j ≤ 1 := pow_le_one₀ (by norm_num) (by norm_num)
    have hεlim : Tendsto ε atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1/2) (by norm_num)
    have hεC : Tendsto (fun j => (ε j : ℂ)) atTop (𝓝 0) := by
      simpa only [Function.comp_def,Complex.ofReal_zero] using Complex.continuous_ofReal.continuousAt.tendsto.comp hεlim
    let U (j : ℕ) := u+(ε j : ℂ)*d
    let V (j : ℕ) := v-(ε j : ℂ)*d/2
    let W (j : ℕ) := w-(ε j : ℂ)*d/2
    let r (j : ℕ) := R+ε j*‖d‖
    let Q (j : ℕ) : Polynomial ℂ := (X-C (U j))*(X-C (V j))*(X-C (W j))
    let P (j : ℕ) := Q j^3
    have hmoment (j : ℕ) : (U j^2+V j^2+W j^2-U j*V j-U j*W j-V j*W j)/3 ≠ 0 :=
      cubic_zero_moment_perturb_nonzero u v w (ε j) (hεpos j) hA hd
    have hdisks (j : ℕ) : ‖U j-o‖ ≤ r j ∧ ‖V j-o‖ ≤ r j ∧ ‖W j-o‖ ≤ r j :=
      cubic_perturbation_disk u v w o d R (ε j) (hεpos j).le hu hv hw
    have hrpos (j : ℕ) : 0 ≤ r j := by dsimp only [r]; positivity
    have hsolutions (j : ℕ) := cubic_triple_nonzero_moment_chain (U j) (V j) (W j) o (r j) (hrpos j)
      (hdisks j).1 (hdisks j).2.1 (hdisks j).2.2 (hmoment j)
    choose z a b hzroot hzstart hztail₀ hztail₁ hzend ha hb hab hmonoA hmonoB hcost using hsolutions
    have hcentroid (j : ℕ) : (U j+V j+W j)/3 = η := by
      dsimp only [U,V,W,η]
      ring
    have hδlim : Tendsto (fun j => (ε j : ℂ)*d) atTop (𝓝 0) := by
      simpa only [zero_mul] using hεC.mul (tendsto_const_nhds (x := d))
    have hUlim : Tendsto U atTop (𝓝 u) := by
      simpa only [U,add_zero] using (tendsto_const_nhds (x := u)).add hδlim
    have hVlim : Tendsto V atTop (𝓝 v) := by
      simpa only [V,zero_div,sub_zero] using (tendsto_const_nhds (x := v)).sub (hδlim.div_const 2)
    have hWlim : Tendsto W atTop (𝓝 w) := by
      simpa only [W,zero_div,sub_zero] using (tendsto_const_nhds (x := w)).sub (hδlim.div_const 2)
    have hQcoeff : ∀ k, Tendsto (fun j => (Q j).coeff k) atTop (𝓝 (q.coeff k)) :=
      polynomial_coeff_mul_tendsto (fun j => (X-C (U j))*(X-C (V j))) (fun j => X-C (W j))
        ((X-C u)*(X-C v)) (X-C w)
        (polynomial_coeff_mul_tendsto (fun j => X-C (U j)) (fun j => X-C (V j)) (X-C u) (X-C v)
          (linear_factor_coeff_tendsto U u hUlim) (linear_factor_coeff_tendsto V v hVlim))
        (linear_factor_coeff_tendsto W w hWlim)
    have hPcoeff : ∀ k, Tendsto (fun j => (P j).coeff k) atTop (𝓝 ((q^3).coeff k)) :=
      polynomial_coeff_pow_tendsto Q q hQcoeff 3
    have hPdeg (j : ℕ) : (P j).natDegree = 9 := triple_cube_natDegree (U j) (V j) (W j)
    have hqdeg : (q^3).natDegree = 9 := triple_cube_natDegree u v w
    let M := R+‖d‖+‖o‖
    have hM : 0 ≤ M := by dsimp only [M]; positivity
    have hrmax (j : ℕ) : r j ≤ R+‖d‖ := by
      have h := mul_le_mul_of_nonneg_right (hεone j) (norm_nonneg d)
      dsimp only [r]
      linarith only [h]
    have hsourceBound (j : ℕ) (x : ℂ) (hx : (P j).eval x = 0) : ‖x‖ ≤ M := by
      have hpow : ((Q j).eval x)^3 = 0 := by simpa only [P,eval_pow] using hx
      have hqroot : (Q j).eval x = 0 := (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hpow
      have hcases : x = U j ∨ x = V j ∨ x = W j := by
        simpa only [Q,eval_mul,eval_sub,eval_X,eval_C,mul_eq_zero,sub_eq_zero,or_assoc] using hqroot
      have hDisk : ‖x-o‖ ≤ r j := by
        rcases hcases with h | h | h
        · rw [h]; exact (hdisks j).1
        · rw [h]; exact (hdisks j).2.1
        · rw [h]; exact (hdisks j).2.2
      have hnorm : ‖x‖ ≤ ‖x-o‖+‖o‖ := by simpa only [sub_add_cancel] using norm_add_le (x-o) o
      change ‖x‖ ≤ R+‖d‖+‖o‖
      linarith only [hnorm,hDisk,hrmax j]
    have hzbound (j : ℕ) (i : Fin 9) : ‖z j i‖ ≤ M :=
      iterate_derivative_norm_bound (P j) (9-(i.val+1)) (by rw [hPdeg]; omega)
        M (hsourceBound j) (z j i) (hzroot j i)
    let costs (j : ℕ) := 4*Real.sqrt 2*r j/3
    have hrLim : Tendsto r atTop (𝓝 R) := by
      simpa only [r,zero_mul,add_zero] using
        (tendsto_const_nhds (x := R)).add (hεlim.mul (tendsto_const_nhds (x := ‖d‖)))
    have hCLim : Tendsto costs atTop (𝓝 (4*Real.sqrt 2*R/3)) :=
      ((tendsto_const_nhds (x := 4*Real.sqrt 2)).mul hrLim).div_const 3
    obtain ⟨f,A,B,hfroot,hfstart,hftail₀,hftail₁,hAunit,hBunit,horth,hmono₀,hmono₁,hfcost⟩ :=
      framed_cube_chain_collision_limit P (q^3) (fun j => (hPdeg j).le) hqdeg.le hPcoeff z a b M hM
        hzbound hzroot η (fun j => (hzstart j).trans (hcentroid j)) hztail₀ hztail₁ ha hb hab
        hmonoA hmonoB costs _ hCLim hcost
    have hqend : q.eval (f 8) = 0 := by
      have h := hfroot 8
      change (q^3).eval (f 8) = 0 at h
      have hp : (q.eval (f 8))^3 = 0 := by simpa only [eval_pow] using h
      exact (pow_eq_zero_iff (by norm_num : (3 : ℕ) ≠ 0)).mp hp
    exact ⟨f,A,B,hfroot,hfstart,hftail₀,hftail₁,hqend,hAunit,hBunit,horth,hmono₀,hmono₁,hfcost⟩

end DerivativeChainPrivate



set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
namespace DerivativeChainPrivate
open Polynomial



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (q : Polynomial ℂ) (hq : q.Monic) (hdeg : q.natDegree = 3)
    (o : ℂ) (R : ℝ) (hR : 0 ≤ R) (hbound : ∀ x : ℂ, q.eval x = 0 → ‖x-o‖ ≤ R) :
    ∃ (z : Fin 9 → ℂ) (a b : ℂ),
      (∀ i, (derivative^[9-(i.val+1)] (q^3)).eval (z i) = 0) ∧
      z 0 = q.roots.sum/3 ∧ z 6 = z 7 ∧ z 7 = z 8 ∧ q.eval (z 8) = 0 ∧
      ‖a‖ = 1 ∧ ‖b‖ = 1 ∧ (a*starRingEnd ℂ b).re = 0 ∧
      Monotone (fun i => (a*z i).re) ∧ Monotone (fun i => (b*z i).re) ∧
      chainCost z ≤ 4*Real.sqrt 2*R/3 := by
  classical
  have hcard : q.roots.card = 3 := by rw [←(IsAlgClosed.splits q).natDegree_eq_card_roots,hdeg]
  obtain ⟨u,v,w,hroots⟩ := Multiset.card_eq_three.mp hcard
  have hfactor : q = (X-C u)*(X-C v)*(X-C w) := by
    rw [(IsAlgClosed.splits q).eq_prod_roots_of_monic hq,hroots]
    simp [mul_assoc]
  have hu : ‖u-o‖ ≤ R := hbound u ((mem_roots hq.ne_zero).mp (by rw [hroots]; simp))
  have hv : ‖v-o‖ ≤ R := hbound v ((mem_roots hq.ne_zero).mp (by rw [hroots]; simp))
  have hw : ‖w-o‖ ≤ R := hbound w ((mem_roots hq.ne_zero).mp (by rw [hroots]; simp))
  have hsol := if hA : (u^2+v^2+w^2-u*v-u*w-v*w)/3 ≠ 0 then
      cubic_triple_nonzero_moment_chain u v w o R hR hu hv hw hA
    else cubic_triple_zero_moment_chain u v w o R hR hu hv hw (by simpa using hA)
  obtain ⟨z,a,b,hzroot,hstart,htail₀,htail₁,hend,ha,hb,hab,hmonoA,hmonoB,hcost⟩ := hsol
  refine ⟨z,a,b,?_,?_,htail₀,htail₁,?_,ha,hb,hab,hmonoA,hmonoB,hcost⟩
  · simpa only [hfactor] using hzroot
  · simpa [hroots,add_assoc] using hstart
  · simpa only [hfactor] using hend
