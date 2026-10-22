-- Prove2me | solution 1 for DQI.Semicircle.eq_132
-- status  : ACCEPTED   (prove)
-- author  : @vebis
-- created : 2026-10-21T17:13:31.119422+00:00
-- url     : https://prove2.me/submissions/1e3be16d-bf4b-43c1-806e-1ef565594976

import Mathlib
import Definitions.Def_DQI_Semicircle_Setting
set_option autoImplicit false

theorem solution (p r m ℓ : ℕ) (hr : 1 ≤ r) (hrp : r < p) (hℓ : 1 ≤ ℓ) (hℓm : ℓ < m)
    (h : (r : ℝ) / p ≤ 1 - (ℓ : ℝ) / m) :
    -((m : ℝ) - 2 * ℓ) / Real.sqrt (ℓ * ((m : ℝ) - ℓ)) ≤ DQI.Semicircle.dparOf p r := by
  unfold DQI.Semicircle.dparOf
  have hr0 : (0 : ℝ) < r := by exact_mod_cast hr
  have hℓ0 : (0 : ℝ) < ℓ := by exact_mod_cast hℓ
  have hb : (0 : ℝ) < (p : ℝ) - r := by
    have : (r : ℝ) < p := by exact_mod_cast hrp
    linarith
  have hd : (0 : ℝ) < (m : ℝ) - ℓ := by
    have : (ℓ : ℝ) < m := by exact_mod_cast hℓm
    linarith
  have hp0 : (0 : ℝ) < p := by linarith
  have hm0 : (0 : ℝ) < m := by linarith
  have hcond : (r : ℝ) * ℓ ≤ ((p : ℝ) - r) * ((m : ℝ) - ℓ) := by
    have h' : (r : ℝ) / p ≤ ((m : ℝ) - ℓ) / m := by
      calc (r : ℝ) / p ≤ 1 - (ℓ : ℝ) / m := h
        _ = ((m : ℝ) - ℓ) / m := by field_simp
    rw [div_le_div_iff₀ hp0 hm0] at h'
    nlinarith
  set u := Real.sqrt r with hu
  set v := Real.sqrt ((p : ℝ) - r) with hv
  set w := Real.sqrt ℓ with hw
  set z := Real.sqrt ((m : ℝ) - ℓ) with hz
  have hu0 : 0 < u := Real.sqrt_pos.mpr hr0
  have hv0 : 0 < v := Real.sqrt_pos.mpr hb
  have hw0 : 0 < w := Real.sqrt_pos.mpr hℓ0
  have hz0 : 0 < z := Real.sqrt_pos.mpr hd
  have hu2 : u ^ 2 = r := Real.sq_sqrt hr0.le
  have hv2 : v ^ 2 = (p : ℝ) - r := Real.sq_sqrt hb.le
  have hw2 : w ^ 2 = ℓ := Real.sq_sqrt hℓ0.le
  have hz2 : z ^ 2 = (m : ℝ) - ℓ := Real.sq_sqrt hd.le
  have e1 : Real.sqrt ((r : ℝ) * ((p : ℝ) - r)) = u * v := Real.sqrt_mul hr0.le _
  have e2 : Real.sqrt ((ℓ : ℝ) * ((m : ℝ) - ℓ)) = w * z := Real.sqrt_mul hℓ0.le _
  have huw : u * w ≤ v * z := by
    have : Real.sqrt ((r : ℝ) * ℓ) ≤ Real.sqrt (((p : ℝ) - r) * ((m : ℝ) - ℓ)) :=
      Real.sqrt_le_sqrt hcond
    rwa [Real.sqrt_mul hr0.le, Real.sqrt_mul hb.le] at this
  rw [e1, e2, div_le_div_iff₀ (mul_pos hw0 hz0) (mul_pos hu0 hv0)]
  have k1 : -((m : ℝ) - 2 * ℓ) = w ^ 2 - z ^ 2 := by rw [hw2, hz2]; ring
  have k2 : (p : ℝ) - 2 * r = v ^ 2 - u ^ 2 := by rw [hv2, hu2]; ring
  rw [k1, k2]
  nlinarith [mul_nonneg (add_nonneg (mul_pos hv0 hw0).le (mul_pos hu0 hz0).le) (sub_nonneg.mpr huw)]
