-- Prove2me | solution 2 for CohnElkies.saddleFirstBranch_normalizedGaussian_exponent_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:22.988348+00:00
-- url     : https://prove2.me/submissions/25df17eb-572c-48d7-8089-bef3cb52be2c

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
    {ℓ V η c C z : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V) (hη : 0 < η)
    (hc : 0 < c) (hC : 0 < C)
    (hupper : η * V ≤ C) :
    (c / (4 * C)) * z ^ 2 ≤
      ((c * ℓ / η) / 4) *
        (z / Real.sqrt (ℓ * V)) ^ 2 := by
  rw [div_pow, Real.sq_sqrt (by positivity)]
  have h : c * ℓ / η / 4 * (z ^ 2 / (ℓ * V)) = c / (4 * (η * V)) * z ^ 2 := by
    field_simp
  rw [h]
  apply mul_le_mul_of_nonneg_right _ (sq_nonneg z)
  apply div_le_div_of_nonneg_left hc.le (by positivity) (by linarith)

