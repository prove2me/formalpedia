-- Prove2me | solution 1 for CohnElkies.saddleSource_scaled_central_radius_le
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-10-19T11:37:30.968836+00:00
-- url     : https://prove2.me/submissions/9569f966-bca8-42cc-9086-b01f23d59895

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
namespace CohnElkies
theorem _root_.solution
    {ℓ η V c U z : ℝ}
    (hℓ : 0 < ℓ) (hη : 0 < η)
    (hc : 0 < c) (hηU : η ≤ U)
    (hz : 0 ≤ z) (hvariance : c ≤ η * V) :
    z / Real.sqrt (ℓ * V) ≤
      (U / Real.sqrt c) *
        (z / Real.sqrt (ℓ * η)) := by
  have hV : 0 < V := by
    nlinarith [hvariance, mul_pos hη hc]
  have hs : 0 < Real.sqrt (ℓ * V) :=
    Real.sqrt_pos.2 (mul_pos hℓ hV)
  have ht : 0 < Real.sqrt (ℓ * η) :=
    Real.sqrt_pos.2 (mul_pos hℓ hη)
  have hw : 0 < Real.sqrt (η * V) :=
    Real.sqrt_pos.2 (mul_pos hη hV)
  have hcroot : 0 < Real.sqrt c :=
    Real.sqrt_pos.2 hc
  have hcross :
      Real.sqrt (ℓ * V) * η =
        Real.sqrt (ℓ * η) * Real.sqrt (η * V) := by
    have heq :
        (Real.sqrt (ℓ * V) * η) ^ 2 =
          (Real.sqrt (ℓ * η) * Real.sqrt (η * V)) ^ 2 := by
      rw [mul_pow, mul_pow,
        Real.sq_sqrt (mul_nonneg hℓ.le hV.le),
        Real.sq_sqrt (mul_nonneg hℓ.le hη.le),
        Real.sq_sqrt (mul_nonneg hη.le hV.le)]
      ring
    nlinarith [mul_pos hs hη, mul_pos ht hw]
  have hwlower : Real.sqrt c ≤ Real.sqrt (η * V) :=
    Real.sqrt_le_sqrt hvariance
  have hU : 0 ≤ U := hη.le.trans hηU
  calc
    z / Real.sqrt (ℓ * V) =
        η * z /
          (Real.sqrt (ℓ * η) * Real.sqrt (η * V)) := by
      field_simp [hs.ne', ht.ne', hw.ne']
      calc
        z * Real.sqrt (ℓ * η) * Real.sqrt (V * η) =
          z * (Real.sqrt (ℓ * η) * Real.sqrt (η * V)) := by
            rw [mul_comm V η]
            ring
        _ = z * (Real.sqrt (ℓ * V) * η) := by
          rw [hcross]
        _ = z * Real.sqrt (ℓ * V) * η := by ring
    _ ≤ U * z /
        (Real.sqrt (ℓ * η) * Real.sqrt c) := by
      gcongr
    _ = (U / Real.sqrt c) *
        (z / Real.sqrt (ℓ * η)) := by
      ring
end CohnElkies
