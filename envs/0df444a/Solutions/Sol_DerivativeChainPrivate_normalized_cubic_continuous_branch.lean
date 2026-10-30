-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_cubic_continuous_branch
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-26T20:14:56.563802+00:00
-- url     : https://prove2.me/submissions/c3740c80-5ff2-48ad-bbcc-f03a00dddd34

import Mathlib
namespace DerivativeChainPrivate
end DerivativeChainPrivate
open DerivativeChainPrivate Filter Topology Polynomial
open scoped BigOperators
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false



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
open Filter Topology Set
namespace DerivativeChainPrivate

theorem monic_small_eval_near_root (p : Polynomial ℂ) (hp : p.Monic)
    (a : ℂ) (ε : ℝ) (hε : 0 < ε) (hsmall : ‖p.eval a‖ < ε ^ p.natDegree) :
    ∃ b : ℂ, p.eval b = 0 ∧ ‖a - b‖ < ε := by
  have hsplit := IsAlgClosed.splits p
  have heval : (p.roots.map (fun b => ‖a - b‖)).prod = ‖p.eval a‖ := by
    calc
      _ = ‖(p.roots.map (fun b => a - b)).prod‖ := by
        change (p.roots.map (fun b => NormedField.toMulRingNorm ℂ (a - b))).prod = _
        rw [p.roots.prod_hom' (NormedField.toMulRingNorm ℂ) (fun b => a - b)]
        rfl
      _ = _ := by rw [hsplit.eval_eq_prod_roots_of_monic hp]
  by_contra! h
  have hlower : ∀ b ∈ p.roots, ε ≤ ‖a - b‖ := by
    intro b hb
    exact h b ((Polynomial.mem_roots hp.ne_zero).mp hb)
  have hprod := Multiset.prod_map_le_prod_map₀ (fun _ : ℂ => ε)
    (fun b => ‖a - b‖) (fun _ _ => hε.le) hlower
  simp only [Multiset.map_const', Multiset.prod_replicate,
    ← hsplit.natDegree_eq_card_roots, heval] at hprod
  exact (not_le_of_gt hsmall) hprod







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
open Filter Topology
namespace DerivativeChainPrivate

theorem positive_polynomial_root_selection_continuous {T : Type*} [TopologicalSpace T]
    (p : T → Polynomial ℂ) (n : ℕ) (hp : ∀ t, (p t).Monic)
    (hdeg : ∀ t, (p t).natDegree = n)
    (heval : ∀ z : ℂ, Continuous (fun t => (p t).eval z))
    (f : T → ℂ) (hfroot : ∀ t, (p t).eval (f t) = 0)
    (hfpos : ∀ t, 0 < (f t).re)
    (hunique : ∀ t z, (p t).eval z = 0 → 0 < z.re → z = f t) : Continuous f := by
  apply continuous_iff_continuousAt.mpr
  intro t
  apply Metric.tendsto_nhds.mpr
  intro ε hε
  let δ := min ε ((f t).re / 2)
  have hδ : 0 < δ := lt_min hε (div_pos (hfpos t) (by norm_num))
  have hE : Tendsto (fun s => ‖(p s).eval (f t)‖) (𝓝 t) (𝓝 0) := by
    simpa only [hfroot, norm_zero] using (heval (f t)).norm.continuousAt.tendsto (x := t)
  filter_upwards [hE.eventually (Iio_mem_nhds (pow_pos hδ n))] with s hs
  obtain ⟨b, hb, hnear⟩ := monic_small_eval_near_root (p s) (hp s) (f t) δ hδ
    (by simpa only [hdeg] using hs)
  have hbr := lt_of_le_of_lt (Complex.re_le_norm (f t - b)) hnear
  simp only [Complex.sub_re] at hbr
  have hbp : 0 < b.re := by
    have hd : δ ≤ (f t).re / 2 := min_le_right _ _
    linarith [hfpos t]
  have hbf := hunique s b hb hbp
  rw [← hbf, dist_eq_norm, norm_sub_rev]
  exact hnear.trans_le (min_le_left _ _)



end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution :
    ∃ f : {β : ℂ // 0 ≤ β.re ∧ 0 ≤ β.im} → ℂ,
      Continuous f ∧ ∀ β,
        f β ^ 3 - f β = β.val ∧ 1 ≤ (f β).re ∧ 0 ≤ (f β).im ∧
        1 + 3 * (f β).im ^ 2 ≤ (f β).re ^ 2 ∧ 3 * f β ^ 2 - 1 ≠ 0 := by
  let f : {β : ℂ // 0 ≤ β.re ∧ 0 ≤ β.im} → ℂ := fun β =>
    (normalized_cubic_quadrant_root β.val β.property.1 β.property.2).exists.choose
  have hf (β : {β : ℂ // 0 ≤ β.re ∧ 0 ≤ β.im}) :
      f β ^ 3 - f β = β.val ∧ 0 < (f β).re :=
    (normalized_cubic_quadrant_root β.val β.property.1 β.property.2).exists.choose_spec
  let p (β : {β : ℂ // 0 ≤ β.re ∧ 0 ≤ β.im}) : Polynomial ℂ :=
    Polynomial.X ^ 3 - Polynomial.X - Polynomial.C β.val
  have hp (β) : (p β).Monic := by
    dsimp only [p]
    monicity!
  have hdeg (β) : (p β).natDegree = 3 := by
    dsimp only [p]
    compute_degree; norm_num
  have hroot (β) : (p β).eval (f β) = 0 := by
    simpa only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
      Polynomial.eval_C, sub_eq_zero] using (hf β).1
  refine ⟨f, ?_, ?_⟩
  · refine positive_polynomial_root_selection_continuous p 3 hp hdeg ?_ f hroot (fun β => (hf β).2) ?_
    · intro z
      simp only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C]
      fun_prop
    · intro β z hz hzpos
      have hzeq : z ^ 3 - z = β.val := by
        simpa only [p, Polynomial.eval_sub, Polynomial.eval_pow, Polynomial.eval_X,
          Polynomial.eval_C, sub_eq_zero] using hz
      exact normalized_cubic_positive_root_unique β.val z (f β)
        β.property.1 β.property.2 hzeq (hf β).1 hzpos (hf β).2
  · intro β
    obtain ⟨hre, him, hsector⟩ := normalized_cubic_positive_root_sector β.val (f β)
      β.property.1 β.property.2 (hf β).1 (hf β).2
    refine ⟨(hf β).1, hre, him, hsector, ?_⟩
    intro hz
    have heq := congrArg Complex.re hz
    norm_num [Complex.sub_re, Complex.mul_re, pow_two] at heq
    nlinarith only [heq, hsector, sq_nonneg (f β).im]
