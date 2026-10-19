-- Prove2me | solution 2 for CohnElkies.saddleSource_scaled_central_radius_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:00:54.213396+00:00
-- url     : https://prove2.me/submissions/76c51866-6ab0-4bcc-9955-4ef938a9e84a

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory intervalIntegral
open scoped Topology


theorem solution
    {ℓ η V c U z : ℝ}
    (hℓ : 0 < ℓ) (hη : 0 < η)
    (hc : 0 < c) (hηU : η ≤ U)
    (hz : 0 ≤ z) (hvariance : c ≤ η * V) :
    z / Real.sqrt (ℓ * V) ≤
      (U / Real.sqrt c) *
        (z / Real.sqrt (ℓ * η)) := by
  have hV : 0 < V := by
    by_contra hcon
    push_neg at hcon
    nlinarith [mul_nonpos_of_nonneg_of_nonpos hη.le hcon]
  have hU : 0 < U := lt_of_lt_of_le hη hηU
  have hA : 0 < Real.sqrt (ℓ * V) := Real.sqrt_pos.mpr (by positivity)
  have hB : 0 < Real.sqrt (ℓ * η) := Real.sqrt_pos.mpr (by positivity)
  have hs : 0 < Real.sqrt c := Real.sqrt_pos.mpr hc
  have key : Real.sqrt c * Real.sqrt (ℓ * η) ≤ U * Real.sqrt (ℓ * V) := by
    rw [← Real.sqrt_mul hc.le, ← Real.sqrt_sq hU.le, ← Real.sqrt_mul (sq_nonneg U)]
    apply Real.sqrt_le_sqrt
    have h1 : c * (ℓ * η) ≤ η * V * (ℓ * η) := mul_le_mul_of_nonneg_right hvariance (by positivity)
    have h2 : η ^ 2 ≤ U ^ 2 := by nlinarith
    have h3 : η ^ 2 * (ℓ * V) ≤ U ^ 2 * (ℓ * V) := mul_le_mul_of_nonneg_right h2 (by positivity)
    nlinarith
  rw [div_mul_div_comm, div_le_div_iff₀ hA (mul_pos hs hB)]
  nlinarith [mul_le_mul_of_nonneg_left key hz]

