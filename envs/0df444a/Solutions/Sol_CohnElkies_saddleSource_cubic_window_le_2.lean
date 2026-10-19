-- Prove2me | solution 2 for CohnElkies.saddleSource_cubic_window_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T11:56:24.114006+00:00
-- url     : https://prove2.me/submissions/0a4006a7-e22d-4048-a5cb-d32712a471eb

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
    {ℓ V M C z T : ℝ}
    (hℓ : 0 < ℓ) (hV : 0 < V)
    (hC : 0 ≤ C) (hz : 0 ≤ z)
    (hM : M ≤ C * V)
    (hT : |T| ≤ z / Real.sqrt (ℓ * V)) :
    (ℓ * M / 6) * |T| ^ 3 ≤
      (C / 6) * z ^ 3 / Real.sqrt (ℓ * V) := by
  have hs : 0 < Real.sqrt (ℓ * V) := Real.sqrt_pos.2 (by positivity)
  have hs2 : Real.sqrt (ℓ * V) ^ 2 = ℓ * V := Real.sq_sqrt (by positivity)
  have hT3 : |T| ^ 3 ≤ (z / Real.sqrt (ℓ * V)) ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hT 3
  have hRHS : (C / 6) * z ^ 3 / Real.sqrt (ℓ * V) =
      (C * Real.sqrt (ℓ * V) ^ 2 / 6) * (z / Real.sqrt (ℓ * V)) ^ 3 := by
    field_simp
  rw [hRHS]
  have hM' : ℓ * M / 6 ≤ C * Real.sqrt (ℓ * V) ^ 2 / 6 := by
    rw [hs2]; nlinarith
  calc ℓ * M / 6 * |T| ^ 3 ≤ C * Real.sqrt (ℓ * V) ^ 2 / 6 * |T| ^ 3 :=
        mul_le_mul_of_nonneg_right hM' (by positivity)
    _ ≤ C * Real.sqrt (ℓ * V) ^ 2 / 6 * (z / Real.sqrt (ℓ * V)) ^ 3 :=
        mul_le_mul_of_nonneg_left hT3 (by positivity)

