-- Prove2me | solution 2 for CohnElkies.upperGammaDampingIntegrand_lower_on_window
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:15:10.705505+00:00
-- url     : https://prove2.me/submissions/a8908fb5-07f5-44a5-87c7-ae8236e43342

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Topology
theorem h47_exp_lt_one {x : ℝ} (h : x < 0) : Real.exp x < 1 := by
  simpa using Real.exp_lt_exp.mpr h

theorem solution
    {ℓ η T a : ℝ}
    (hℓ : 0 < ℓ) (hη : 0 < η)
    (ha : 0 < a)
    (haη : a ≤ η⁻¹)
    (haT : a ≤ |T|⁻¹)
    (hT : T ≠ 0) :
    (ℓ / (8 * Real.exp 1)) * T ^ 2 ≤
      upperGammaDampingIntegrand ℓ η T a := by
  unfold upperGammaDampingIntegrand upperGammaMeasureDensity
  have hT' : 0 < |T| := abs_pos.mpr hT
  have haT1 : |a * T| ≤ 1 := by
    rw [abs_mul, abs_of_pos ha]
    calc a * |T| ≤ |T|⁻¹ * |T| := mul_le_mul_of_nonneg_right haT hT'.le
      _ = 1 := inv_mul_cancel₀ hT'.ne'
  have hcos : (a * T) ^ 2 / 4 ≤ 1 - Real.cos (a * T) := by
    have h := Real.cos_bound haT1
    have h2 : (a * T) ^ 2 ≤ 1 := by nlinarith [abs_nonneg (a * T), sq_abs (a * T)]
    have h4 : |a * T| ^ 4 = ((a * T) ^ 2) ^ 2 := by
      rw [show (4:ℕ) = 2 * 2 from rfl, pow_mul, sq_abs]
    rw [h4] at h
    have := (abs_le.mp h).2
    nlinarith [sq_nonneg (a * T)]
  have hηa : η * a ≤ 1 := by
    have := mul_le_mul_of_nonneg_left haη hη.le
    rwa [mul_inv_cancel₀ hη.ne'] at this
  have hexp : Real.exp (-1) ≤ Real.exp (-η * a) := Real.exp_le_exp.mpr (by linarith)
  have hx : 0 < 2 * a / ℓ := by positivity
  have hden1 : 1 - Real.exp (-(2 * a / ℓ)) ≤ 2 * a / ℓ := by
    linarith [Real.add_one_le_exp (-(2 * a / ℓ))]
  have hden0 : 0 < 1 - Real.exp (-(2 * a / ℓ)) := by
    have := h47_exp_lt_one (by linarith : -(2 * a / ℓ) < 0)
    linarith
  have hD : 0 < a * (1 - Real.exp (-(2 * a / ℓ))) := mul_pos ha hden0
  have hD2 : a * (1 - Real.exp (-(2 * a / ℓ))) ≤ 2 * a ^ 2 / ℓ := by
    calc _ ≤ a * (2 * a / ℓ) := mul_le_mul_of_nonneg_left hden1 ha.le
      _ = _ := by ring
  have he : Real.exp (-1) = (Real.exp 1)⁻¹ := Real.exp_neg 1
  rw [mul_div_assoc', le_div_iff₀ hD]
  calc ℓ / (8 * Real.exp 1) * T ^ 2 * (a * (1 - Real.exp (-(2 * a / ℓ))))
      ≤ ℓ / (8 * Real.exp 1) * T ^ 2 * (2 * a ^ 2 / ℓ) :=
        mul_le_mul_of_nonneg_left hD2
          (mul_nonneg (div_nonneg hℓ.le (by positivity)) (sq_nonneg T))
    _ = (a * T) ^ 2 / 4 * Real.exp (-1) := by
        rw [he]
        first
          | (field_simp; ring)
          | field_simp
    _ ≤ (1 - Real.cos (a * T)) * Real.exp (-η * a) :=
        mul_le_mul hcos hexp (Real.exp_pos _).le (by nlinarith [sq_nonneg (a * T)])

