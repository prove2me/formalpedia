-- Prove2me | solution 1 for CongestionApproxPNE.display_5
-- status  : ACCEPTED   (prove)
-- author  : @shivm
-- created : 2026-11-07T20:58:16.856254+00:00
-- url     : https://prove2.me/submissions/65c90ff3-b956-49e5-b1c9-51ac8b7271fb

import Mathlib
import Definitions.Def_CongestionApproxPNE_kd
import Definitions.Def_CongestionApproxPNE_wChoice
import Definitions.Def_CongestionApproxPNE_betaChoice
import Definitions.Def_CongestionApproxPNE_nChoice

set_option autoImplicit false

open CongestionApproxPNE in
theorem solution (d : ℕ) (hd : 4 ≤ d) :
    (1 + (nChoice d : ℝ) * wChoice d) ^ kd d + (nChoice d : ℝ) * betaChoice d ≤
      (1 + (d : ℝ) ^ (-(1 / (2 * ((kd d : ℝ) + 1))))) ^ kd d +
        2 * Real.sqrt d / (Real.log d * (1 + Real.log d / (2 * d)) ^ d) := by
  have hD : (4 : ℝ) ≤ d := by exact_mod_cast hd
  have hD0 : (0 : ℝ) < d := by linarith
  have hlog : 0 < Real.log d := Real.log_pos (by linarith)
  have hwd : wChoice d = Real.log d / (2 * d) := rfl
  have hw : 0 < wChoice d := by rw [hwd]; positivity
  have hβ : betaChoice d = 1 / ((d : ℝ) ^ ((kd d : ℝ) / (2 * ((kd d : ℝ) + 1))) *
      (1 + wChoice d) ^ d) := rfl
  obtain ⟨a, ha⟩ : ∃ a : ℝ, a = 1 / (2 * ((kd d : ℝ) + 1)) := ⟨_, rfl⟩
  obtain ⟨b, hb⟩ : ∃ b : ℝ, b = (kd d : ℝ) / (2 * ((kd d : ℝ) + 1)) := ⟨_, rfl⟩
  have hNd : (nChoice d : ℝ) ≤ 1 / ((d : ℝ) ^ (1 / (2 * ((kd d : ℝ) + 1))) * wChoice d) :=
    Nat.floor_le (div_pos one_pos (mul_pos (Real.rpow_pos_of_pos hD0 _) hw)).le
  rw [← ha] at hNd ⊢
  rw [← hb] at hβ
  have hda : 0 < (d : ℝ) ^ a := Real.rpow_pos_of_pos hD0 a
  have hdb : 0 < (d : ℝ) ^ b := Real.rpow_pos_of_pos hD0 b
  have hP : 0 < (1 + wChoice d) ^ d := pow_pos (by linarith) d
  have hNw : (nChoice d : ℝ) * wChoice d ≤ (d : ℝ) ^ (-a) := by
    rw [Real.rpow_neg hD0.le]
    calc (nChoice d : ℝ) * wChoice d ≤ 1 / ((d : ℝ) ^ a * wChoice d) * wChoice d :=
          mul_le_mul_of_nonneg_right hNd hw.le
      _ = ((d : ℝ) ^ a)⁻¹ := by
          rw [one_div, mul_inv, mul_assoc, inv_mul_cancel₀ hw.ne', mul_one]
  have h1 : (1 + (nChoice d : ℝ) * wChoice d) ^ kd d ≤ (1 + (d : ℝ) ^ (-a)) ^ kd d := by
    have := mul_nonneg (Nat.cast_nonneg (α := ℝ) (nChoice d)) hw.le
    exact pow_le_pow_left₀ (by linarith) (by linarith) _
  have hab : (d : ℝ) ^ a * (d : ℝ) ^ b = Real.sqrt d := by
    rw [← Real.rpow_add hD0, Real.sqrt_eq_rpow]
    congr 1
    rw [ha, hb, ← add_div, div_eq_div_iff (by positivity) (by norm_num)]
    ring
  have hβ0 : 0 ≤ betaChoice d := by rw [hβ]; positivity
  have h2 : (nChoice d : ℝ) * betaChoice d ≤
      2 * Real.sqrt d / (Real.log d * (1 + Real.log d / (2 * d)) ^ d) := by
    calc (nChoice d : ℝ) * betaChoice d
        ≤ 1 / ((d : ℝ) ^ a * wChoice d) * betaChoice d := mul_le_mul_of_nonneg_right hNd hβ0
      _ = 2 * Real.sqrt d / (Real.log d * (1 + Real.log d / (2 * d)) ^ d) := by
          rw [hβ, ← hwd]
          have e : 1 / ((d : ℝ) ^ a * wChoice d) * (1 / ((d : ℝ) ^ b * (1 + wChoice d) ^ d))
              = 1 / (((d : ℝ) ^ a * (d : ℝ) ^ b) * wChoice d * (1 + wChoice d) ^ d) := by
            rw [div_mul_div_comm, one_mul]
            congr 1
            ring
          rw [e, hab]
          have hs : 0 < Real.sqrt d := Real.sqrt_pos.mpr hD0
          have hsq : (d : ℝ) = Real.sqrt d * Real.sqrt d := (Real.mul_self_sqrt hD0.le).symm
          generalize (1 + wChoice d) ^ d = P at hP ⊢
          rw [hwd]
          generalize Real.log (d : ℝ) = L at hlog ⊢
          generalize Real.sqrt (d : ℝ) = s at hs hsq ⊢
          rw [hsq]
          first | (field_simp; done) | (field_simp; ring)
  linarith [add_le_add h1 h2]
