-- Prove2me | solution 1 for CohnElkies.plusPolynomial_imaginary_cubic_growth_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:25.301796+00:00
-- url     : https://prove2.me/submissions/1563dcf1-b1e1-4741-9663-520633f64d7b

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_plusPolynomial_imaginary_norm_ge_beta

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
    {ε u : ℝ} (hε : 0 < ε) (hu : -1 ≤ u) :
    (1 + |u|) ^ 3 ≤
      (27 / beta ε + 9) *
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
  have hb : 0 < beta ε := beta_pos hε
  have hnorm :
      beta ε ≤ ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
    plusPolynomial_imaginary_norm_ge_beta hε hu
  by_cases hbounded : u ≤ 2
  · have habs : |u| ≤ 2 := by
      exact (abs_le).mpr ⟨by linarith, hbounded⟩
    have hcube : (1 + |u|) ^ 3 ≤ 27 := by
      have hbase : 1 + |u| ≤ (3 : ℝ) := by linarith
      have hpow := pow_le_pow_left₀
        (show 0 ≤ 1 + |u| by positivity) hbase 3
      norm_num at hpow ⊢
      exact hpow
    calc
      (1 + |u|) ^ 3 ≤ 27 := hcube
      _ = (27 / beta ε) * beta ε := by
        field_simp [hb.ne']
      _ ≤ (27 / beta ε) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ :=
        mul_le_mul_of_nonneg_left hnorm (by positivity)
      _ ≤ (27 / beta ε + 9) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
        have hnonnegative :=
          norm_nonneg (plusPolynomial ε (Complex.I * (u : ℂ)))
        nlinarith
  · have hlarge : 2 < u := lt_of_not_ge hbounded
    have habs : |u| = u := abs_of_pos (by linarith)
    have hvalue :
        ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ =
          beta ε + (1 - u) ^ 2 * (1 + u) := by
      rw [plusPolynomial_imaginary, Complex.norm_real,
        Real.norm_eq_abs]
      apply abs_of_pos
      exact add_pos_of_pos_of_nonneg hb
        (mul_nonneg (sq_nonneg _) (by linarith))
    have hsq :
        (1 + u) ^ 2 ≤ 9 * (1 - u) ^ 2 := by
      have hfactor : 0 ≤ (2 * u - 1) * (u - 2) :=
        mul_nonneg (by linarith) (by linarith)
      nlinarith
    have hcube :
        (1 + u) ^ 3 ≤
          9 * ((1 - u) ^ 2 * (1 + u)) := by
      have hproduct := mul_le_mul_of_nonneg_right
        hsq (show 0 ≤ 1 + u by linarith)
      nlinarith
    rw [habs]
    calc
      (1 + u) ^ 3 ≤
          9 * ((1 - u) ^ 2 * (1 + u)) := hcube
      _ ≤ 9 * ‖plusPolynomial ε
          (Complex.I * (u : ℂ))‖ := by
        rw [hvalue]
        nlinarith
      _ ≤ (27 / beta ε + 9) *
          ‖plusPolynomial ε (Complex.I * (u : ℂ))‖ := by
        have hnonnegative :=
          norm_nonneg (plusPolynomial ε (Complex.I * (u : ℂ)))
        have hcoefficient : 0 ≤ 27 / beta ε := by
          positivity
        nlinarith [mul_nonneg hcoefficient hnonnegative]
end CohnElkies
