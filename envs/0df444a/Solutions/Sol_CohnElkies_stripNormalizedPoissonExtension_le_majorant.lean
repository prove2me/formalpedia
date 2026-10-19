-- Prove2me | solution 1 for CohnElkies.stripNormalizedPoissonExtension_le_majorant
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:24.652437+00:00
-- url     : https://prove2.me/submissions/6881f0e8-2249-400e-ae3a-47caa4c09d14

import Mathlib
import Definitions.Def_SpherePacking
import Theorems.Thm_CohnElkies_inv_cosh_le_two_exp_neg_abs

set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology
namespace CohnElkies
theorem _root_.solution
    {σ : ℝ} (hzero : 0 ≤ σ) (hone : σ ≤ 1) (T : ℝ) :
    0 ≤ stripNormalizedPoissonExtension σ T ∧
      stripNormalizedPoissonExtension σ T ≤
        stripPoissonExponentialMajorant T := by
  let u : ℝ := Real.pi * T / 2
  let q : ℝ := Real.pi * (1 - σ) / 2
  have hqzero : 0 ≤ q := by
    try dsimp [q]
    exact div_nonneg (mul_nonneg Real.pi_pos.le (sub_nonneg.mpr hone))
      (by norm_num)
  have hqlarge : q ≤ Real.pi / 2 := by
    try dsimp [q]
    nlinarith [mul_nonneg Real.pi_pos.le hzero]
  have hqpi : q ≤ Real.pi := by
    linarith [Real.pi_pos]
  have hcos : 0 ≤ Real.cos q :=
    Real.cos_nonneg_of_mem_Icc
      ⟨by linarith [Real.pi_pos], hqlarge⟩
  have hsinc : 0 ≤ Real.sinc q := by
    by_cases hq : q = 0
    · simp [hq]
    · rw [Real.sinc_of_ne_zero hq]
      exact div_nonneg
        (Real.sin_nonneg_of_nonneg_of_le_pi hqzero hqpi) hqzero
  have hden : 0 < Real.cosh u + Real.cos q :=
    add_pos_of_pos_of_nonneg (Real.cosh_pos u) hcos
  have hcoefficient : 0 < Real.pi / 4 :=
    div_pos Real.pi_pos (by norm_num)
  have habsu : |u| = (Real.pi / 2) * |T| := by
    try dsimp [u]
    rw [abs_div, abs_mul, abs_of_pos Real.pi_pos]
    norm_num
    ring
  constructor
  · unfold stripNormalizedPoissonExtension
    change 0 ≤ (Real.pi / 4) * Real.sinc q /
      (Real.cosh u + Real.cos q)
    exact div_nonneg (mul_nonneg hcoefficient.le hsinc) hden.le
  · unfold stripNormalizedPoissonExtension
      stripPoissonExponentialMajorant
    change
      (Real.pi / 4) * Real.sinc q /
        (Real.cosh u + Real.cos q) ≤
          (Real.pi / 2) *
            Real.exp (-(Real.pi / 2) * |T|)
    calc
      (Real.pi / 4) * Real.sinc q /
          (Real.cosh u + Real.cos q) ≤
        (Real.pi / 4) * 1 / Real.cosh u := by
          gcongr
          · exact Real.sinc_le_one q
          · exact le_add_of_nonneg_right hcos
      _ = (Real.pi / 4) * (Real.cosh u)⁻¹ := by
        simp [div_eq_mul_inv]
      _ ≤ (Real.pi / 4) * (2 * Real.exp (-|u|)) :=
        mul_le_mul_of_nonneg_left
          (inv_cosh_le_two_exp_neg_abs u) hcoefficient.le
      _ = (Real.pi / 2) *
          Real.exp (-(Real.pi / 2) * |T|) := by
        rw [habsu]
        ring_nf
end CohnElkies
