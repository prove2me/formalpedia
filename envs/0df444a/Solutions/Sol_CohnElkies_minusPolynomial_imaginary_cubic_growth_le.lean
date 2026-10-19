-- Prove2me | solution 1 for CohnElkies.minusPolynomial_imaginary_cubic_growth_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/943748e2-a342-4d52-9535-aac997e1a257

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_re_neg
import Theorems.Thm_CohnElkies_minusPolynomial_imaginary_norm_ge_three_beta

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
namespace CohnElkies
theorem _root_.solution
    {ε u : ℝ} (hε : 0 < ε)
    (hu : 1 + ε / 4 ≤ u) :
    (1 + |u|) ^ 3 ≤
      (9 / beta ε + 6) *
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have hb : 0 < beta ε := beta_pos hε
  have hone : 1 ≤ u := by linarith
  have hbeta : beta ε ≤ u - 1 := by
    unfold beta
    linarith
  have habs : |u| = u := abs_of_pos (by linarith)
  have hnorm := minusPolynomial_imaginary_norm_ge_three_beta
    hε hu
  by_cases hbounded : u ≤ 2
  · have hcube : (1 + |u|) ^ 3 ≤ 27 := by
      have hbase : 1 + |u| ≤ (3 : ℝ) := by
        rw [habs]
        linarith
      have hpow := pow_le_pow_left₀
        (show 0 ≤ 1 + |u| by positivity) hbase 3
      norm_num at hpow ⊢
      exact hpow
    calc
      (1 + |u|) ^ 3 ≤ 27 := hcube
      _ = (9 / beta ε) * (3 * beta ε) := by
        field_simp [hb.ne']; norm_num
      _ ≤ (9 / beta ε) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ (9 / beta ε + 6) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
        have hnonnegative :=
          norm_nonneg (minusPolynomial ε
            (Complex.I * (u : ℂ)))
        nlinarith
  · have hlarge : 2 < u := lt_of_not_ge hbounded
    have hnegative := minusPolynomial_imaginary_re_neg hε hu
    have hvalue :
        ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ =
          (u - 1) * (1 + u) ^ 2 - beta ε := by
      rw [minusPolynomial_imaginary, Complex.norm_real,
        Real.norm_eq_abs]
      have harg : beta ε + (1 - u) * (1 + u) ^ 2 < 0 := by
        rw [minusPolynomial_imaginary, Complex.ofReal_re]
          at hnegative
        exact hnegative
      rw [abs_of_neg harg]
      ring
    have hsquare : (4 : ℝ) ≤ (1 + u) ^ 2 := by
      nlinarith [sq_nonneg (u - 1)]
    have hterm :
        2 * beta ε ≤ (u - 1) * (1 + u) ^ 2 := by
      calc
        2 * beta ε ≤ 4 * beta ε := by nlinarith
        _ = beta ε * 4 := by ring
        _ ≤ (u - 1) * (1 + u) ^ 2 :=
          mul_le_mul hbeta hsquare (by norm_num) (by linarith)
    have hlinear : 1 + u ≤ 3 * (u - 1) := by
      linarith
    have hcubic :
        (1 + u) ^ 3 ≤
          3 * ((u - 1) * (1 + u) ^ 2) := by
      have hproduct :=
        mul_le_mul_of_nonneg_right hlinear (sq_nonneg (1 + u))
      nlinarith
    rw [habs]
    calc
      (1 + u) ^ 3 ≤
          3 * ((u - 1) * (1 + u) ^ 2) := hcubic
      _ ≤ 6 * ‖minusPolynomial ε
          (Complex.I * (u : ℂ))‖ := by
        rw [hvalue]
        nlinarith
      _ ≤ (9 / beta ε + 6) *
          ‖minusPolynomial ε (Complex.I * (u : ℂ))‖ := by
        have hnonnegative :=
          norm_nonneg (minusPolynomial ε
            (Complex.I * (u : ℂ)))
        have hcoefficient : 0 ≤ 9 / beta ε := by
          positivity
        nlinarith [mul_nonneg hcoefficient hnonnegative]
end CohnElkies
