-- Prove2me | solution 2 for CohnElkies.saddleFirstBranch_normalizedGaussian_prefactor_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:26:23.570045+00:00
-- url     : https://prove2.me/submissions/39e8a5c1-97df-453e-9e0f-1187cbe19c7f

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology


theorem solution
    {ℓ V η c C : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hη : 0 < η)
    (hc : 0 < c)
    (hupper : η * V ≤ C) :
    Real.sqrt (ℓ * V) *
        Real.sqrt (Real.pi / ((c * ℓ / η) / 4)) ≤
      2 * Real.sqrt (Real.pi * C / c) := by
  rw [← Real.sqrt_mul (by positivity)]
  have h4 : 2 * Real.sqrt (Real.pi * C / c) = Real.sqrt (4 * (Real.pi * C / c)) := by
    rw [Real.sqrt_mul (by norm_num), show (4:ℝ) = 2^2 by norm_num, Real.sqrt_sq (by norm_num)]
  rw [h4]
  apply Real.sqrt_le_sqrt
  have h : ℓ * V * (Real.pi / ((c * ℓ / η) / 4)) = 4 * (Real.pi * (η * V) / c) := by
    field_simp
  rw [h]
  have := Real.pi_pos
  gcongr

