-- Prove2me | solution 1 for DerivativeChainPrivate.compressed_quadratic_actual_reset
-- status  : ACCEPTED   (prove)
-- author  : @labuka
-- created : 2026-10-19T05:05:36.735827+00:00
-- url     : https://prove2.me/submissions/f83d2cbb-3a1f-4f98-a817-b5fe8480f2f8

import Mathlib
import Definitions.Def_DerivativeChainPrivate_foundations
open Polynomial DerivativeChainPrivate
set_option autoImplicit false



set_option autoImplicit false

namespace DerivativeChainPrivate
open Polynomial















end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators

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

theorem choose_blocks_power_lower (M q d : ℕ) :
    (M.choose q) ^ d ≤ (M * d).choose (q * d) := by
  induction d with
  | zero => simp
  | succ d ih =>
    have hterm : (M * d).choose (q * d) * M.choose q ≤
        (M * d + M).choose (q * d + q) := by
      rw [Nat.add_choose_eq]
      exact Finset.single_le_sum (fun ij _ => Nat.zero_le
        ((M * d).choose ij.1 * M.choose ij.2))
        (show (q * d, q) ∈ Finset.HasAntidiagonal.antidiagonal (q * d + q) by simp)
    calc
      (M.choose q) ^ (d + 1) = (M.choose q) ^ d * M.choose q := pow_succ _ _
      _ ≤ (M * d).choose (q * d) * M.choose q := Nat.mul_le_mul_right _ ih
      _ ≤ (M * (d + 1)).choose (q * (d + 1)) := by
        simpa [Nat.mul_add] using hterm





theorem quadratic_radius_from_coefficient_bound (x : ℝ) (n M d : ℕ)
    (hx : 0 ≤ x) (hM : 3 ≤ M) (hd : 2 ≤ d) (hn : M * d ≤ n)
    (hcoeff : (n.choose (2 * d) : ℝ) * x ^ (2 * d) ≤ M.choose 2) :
    x ≤ 4 / 5 := by
  have hc : (3 : ℝ) ≤ M.choose 2 := by
    exact_mod_cast (show 3 ≤ M.choose 2 from by
      simpa using Nat.choose_le_choose 2 hM)
  have hchoose : ((M.choose 2 : ℝ) ^ d) ≤ n.choose (2 * d) := by
    exact_mod_cast ((choose_blocks_power_lower M 2 d).trans
      (Nat.choose_le_choose (2 * d) hn))
  have hbound : ((M.choose 2 : ℝ) * x ^ 2) ^ d ≤ M.choose 2 := by
    rw [mul_pow, ← pow_mul]
    exact (mul_le_mul_of_nonneg_right hchoose (by positivity)).trans hcoeff
  by_contra h
  have hlarge : 4 / 5 < x := lt_of_not_ge h
  have hx2 : 16 / 25 < x ^ 2 := by nlinarith
  have hx4 : 256 / 625 < (x ^ 2) ^ 2 := by nlinarith [sq_nonneg (x ^ 2 - 16 / 25)]
  have hcpos : (0 : ℝ) < M.choose 2 := by linarith
  have hcprod : 3 * x ^ 2 ≤ (M.choose 2 : ℝ) * x ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg x)
  have hbase : 1 ≤ (M.choose 2 : ℝ) * x ^ 2 := by nlinarith
  have hpow := (pow_le_pow_right₀ hbase hd).trans hbound
  have hmul : 3 * (x ^ 2) ^ 2 ≤ (M.choose 2 : ℝ) * (x ^ 2) ^ 2 :=
    mul_le_mul_of_nonneg_right hc (sq_nonneg (x ^ 2))
  have hgt : 0 < (M.choose 2 : ℝ) * (x ^ 2) ^ 2 - 1 := by nlinarith
  nlinarith [mul_pos hcpos hgt]

end DerivativeChainPrivate



set_option autoImplicit false
namespace DerivativeChainPrivate

theorem equal_radius_detour (w z : ℂ)
    (hsupport : ‖z‖ ^ 2 ≤ (w * starRingEnd ℂ z).re) :
    ‖z‖ + ‖w - z‖ ≤ Real.sqrt 2 * ‖w‖ := by
  have hid : ‖w - z‖ ^ 2 = ‖w‖ ^ 2 + ‖z‖ ^ 2 -
      2 * (w * starRingEnd ℂ z).re := by
    simp only [Complex.sq_norm, Complex.normSq_apply, Complex.sub_re,
      Complex.sub_im, Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  have htwo : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg 2
  have htwo2 : Real.sqrt 2 ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  have hnonneg : 0 ≤ ‖z‖ + ‖w - z‖ := by positivity
  have hsq : (‖z‖ + ‖w - z‖) ^ 2 ≤ 2 * ‖w‖ ^ 2 := by
    nlinarith [sq_nonneg (‖z‖ - ‖w - z‖)]
  have hright : 0 ≤ Real.sqrt 2 * ‖w‖ := by positivity
  nlinarith [sq_nonneg (‖z‖ + ‖w - z‖ + Real.sqrt 2 * ‖w‖)]

theorem compressed_quadratic_detour_budget (a R cost : ℝ)
    (ha : 0 ≤ a) (hsmall : a ≤ (4 / 5 : ℝ) * R)
    (hcost : cost ≤ Real.sqrt 2 * a) :
    cost + a + R ≤ 3 * R := by
  have hsqrt : Real.sqrt 2 ≤ (3 / 2 : ℝ) := by
    apply Real.sqrt_le_iff.mpr
    norm_num
  nlinarith

theorem compressed_quadratic_reset_bound (w z : ℂ) (R : ℝ)
    (hsupport : ‖z‖ ^ 2 ≤ (w * starRingEnd ℂ z).re)
    (hsmall : ‖w‖ ≤ (4 / 5 : ℝ) * R) :
    ‖z‖ + ‖w - z‖ + ‖w‖ + R ≤ 3 * R := by
  exact compressed_quadratic_detour_budget ‖w‖ R (‖z‖ + ‖w - z‖)
    (norm_nonneg _) hsmall (equal_radius_detour w z hsupport)

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





end DerivativeChainPrivate



set_option autoImplicit false
open scoped BigOperators
namespace DerivativeChainPrivate









end DerivativeChainPrivate

open DerivativeChainPrivate in
theorem solution (p : Polynomial ℂ)
    (hdegree : 2 ≤ p.natDegree) (z : ℂ) (hz : p.derivative.eval z = 0)
    (n M d : ℕ) (hM : 3 ≤ M) (hd : 2 ≤ d) (hn : M * d ≤ n)
    (hcoeff : ∀ w : ℂ, p.eval w = 0 →
      (n.choose (2 * d) : ℝ) * ‖w‖ ^ (2 * d) ≤ M.choose 2) :
    ∃ w : ℂ, p.eval w = 0 ∧ ‖z‖ + ‖w - z‖ + ‖w‖ + 1 ≤ 3 := by
  obtain ⟨w, hw, hs⟩ := derivative_supporting_parent p hdegree z hz
  have hsmall := quadratic_radius_from_coefficient_bound ‖w‖ n M d
    (norm_nonneg _) hM hd hn (hcoeff w hw)
  exact ⟨w, hw, by simpa using compressed_quadratic_reset_bound w z 1 hs (by simpa using hsmall)⟩
