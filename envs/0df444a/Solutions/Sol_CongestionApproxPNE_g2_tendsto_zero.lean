-- Prove2me | solution 1 for CongestionApproxPNE.g2_tendsto_zero
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-20T21:00:24.186936+00:00
-- url     : https://prove2.me/submissions/9b77bd0c-ec01-452b-9497-3fafa3ceaf42

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd

set_option autoImplicit false

open Filter Topology

namespace Aux_CongestionApproxPNE_g2_tendsto_zero

lemma key (d : ℕ) (hd : 2 ≤ d) :
    0 ≤ 2 * Real.sqrt (d : ℝ) / ((1 + Real.log (d : ℝ) / (2 * (d : ℝ))) ^ d * Real.log (d : ℝ)) ∧
    2 * Real.sqrt (d : ℝ) / ((1 + Real.log (d : ℝ) / (2 * (d : ℝ))) ^ d * Real.log (d : ℝ)) ≤
      2 * Real.exp 1 / Real.log (d : ℝ) := by
  have hD : (2 : ℝ) ≤ (d : ℝ) := by exact_mod_cast hd
  obtain ⟨D, hDdef⟩ : ∃ D : ℝ, D = (d : ℝ) := ⟨_, rfl⟩
  rw [← hDdef] at hD ⊢
  have hDpos : 0 < D := by linarith
  have hx : 0 < Real.log D := Real.log_pos (by linarith)
  have hs : 0 < Real.sqrt D := Real.sqrt_pos.mpr hDpos
  have hsq : Real.sqrt D ^ 2 = D := Real.sq_sqrt hDpos.le
  have hlogs : Real.log (Real.sqrt D) = Real.log D / 2 := Real.log_sqrt hDpos.le
  have hxs : Real.log D ≤ 2 * Real.sqrt D := by
    have := Real.log_le_sub_one_of_pos hs
    linarith
  obtain ⟨x, hxdef⟩ : ∃ x : ℝ, x = Real.log D := ⟨_, rfl⟩
  rw [← hxdef] at hx hlogs hxs ⊢
  obtain ⟨y, hydef⟩ : ∃ y : ℝ, y = x / (2 * D) := ⟨_, rfl⟩
  rw [← hydef]
  have hy : 0 ≤ y := by rw [hydef]; exact div_nonneg hx.le (by linarith)
  have hDy : D * y = x / 2 := by
    rw [hydef, mul_div_assoc', div_eq_div_iff (ne_of_gt (by linarith)) (by norm_num)]
    ring
  have hxy : x * y ≤ 2 := by
    have hxx : x * x ≤ 4 * D := by
      nlinarith [mul_le_mul hxs hxs hx.le (by linarith : (0 : ℝ) ≤ 2 * Real.sqrt D)]
    rw [hydef, mul_div_assoc', div_le_iff₀ (by linarith : (0 : ℝ) < 2 * D)]
    linarith
  have h1y : 0 < 1 + y := by linarith
  have hL : y ≤ (1 + y) * Real.log (1 + y) := by
    have h := Real.one_sub_inv_le_log_of_pos h1y
    have h2 := mul_le_mul_of_nonneg_left h h1y.le
    have h3 := mul_inv_cancel₀ h1y.ne'
    nlinarith
  have hkey : x / 2 - 1 ≤ D * Real.log (1 + y) := by
    have h2 : (x / 2 - 1) * (1 + y) ≤ (D * Real.log (1 + y)) * (1 + y) := by
      have h4 := mul_le_mul_of_nonneg_left hL hDpos.le
      nlinarith
    exact le_of_mul_le_mul_right h2 h1y
  have hP : (1 + y) ^ d = Real.exp (D * Real.log (1 + y)) := by
    rw [← Real.exp_log (pow_pos h1y d), Real.log_pow, hDdef]
  have hP0 : 0 < (1 + y) ^ d := pow_pos h1y d
  have hsqrt_le : Real.sqrt D ≤ Real.exp 1 * (1 + y) ^ d := by
    have e1 : Real.sqrt D = Real.exp (x / 2) := by rw [← hlogs, Real.exp_log hs]
    have e2 : Real.exp (x / 2) = Real.exp 1 * Real.exp (x / 2 - 1) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [e1, e2, hP]
    exact mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr hkey) (Real.exp_pos 1).le
  constructor
  · exact div_nonneg (by positivity) (mul_nonneg hP0.le hx.le)
  · rw [div_le_div_iff₀ (mul_pos hP0 hx) hx]
    nlinarith [mul_le_mul_of_nonneg_right hsqrt_le hx.le]

end Aux_CongestionApproxPNE_g2_tendsto_zero

open Aux_CongestionApproxPNE_g2_tendsto_zero in
theorem solution :
    Tendsto (fun d : ℕ => 2 * Real.sqrt d / ((1 + Real.log d / (2 * d)) ^ d * Real.log d))
      atTop (𝓝 0) := by
  have hlog : Tendsto (fun d : ℕ => Real.log (d : ℝ)) atTop atTop :=
    Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
  have hup : Tendsto (fun d : ℕ => 2 * Real.exp 1 / Real.log (d : ℝ)) atTop (𝓝 0) :=
    tendsto_const_nhds.div_atTop hlog
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hup ?_ ?_
  · filter_upwards [eventually_ge_atTop 2] with d hd using (key d hd).1
  · filter_upwards [eventually_ge_atTop 2] with d hd using (key d hd).2
