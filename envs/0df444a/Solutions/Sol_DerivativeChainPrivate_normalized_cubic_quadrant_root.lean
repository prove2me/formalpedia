-- Prove2me | solution 1 for DerivativeChainPrivate.normalized_cubic_quadrant_root
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-27T03:32:25.867399+00:00
-- url     : https://prove2.me/submissions/b541e7ce-c885-4886-8f71-d762f90345f0

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
import Theorems.Thm_DerivativeChainPrivate_normalized_cubic_positive_root_sector
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



open DerivativeChainPrivate in
theorem solution (β : ℂ)
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
