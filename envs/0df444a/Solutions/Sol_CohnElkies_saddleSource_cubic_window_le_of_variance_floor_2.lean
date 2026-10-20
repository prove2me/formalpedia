-- Prove2me | solution 2 for CohnElkies.saddleSource_cubic_window_le_of_variance_floor
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:29:45.016133+00:00
-- url     : https://prove2.me/submissions/aa1783ee-8fc8-4dd4-b3f5-2fef0e7652af

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
    {ℓ V M C V₀ z T : ℝ}
    (hℓ : 0 < ℓ) (hV₀ : 0 < V₀)
    (hfloor : V₀ ≤ V)
    (hC : 0 ≤ C) (hz : 0 ≤ z)
    (hM : M ≤ C * V)
    (hT : |T| ≤ z / Real.sqrt (ℓ * V)) :
    (ℓ * M / 6) * |T| ^ 3 ≤
      (C / 6) * z ^ 3 /
        (Real.sqrt ℓ * Real.sqrt V₀) := by
  have hV : 0 < V := lt_of_lt_of_le hV₀ hfloor
  have hs : 0 < Real.sqrt (ℓ * V) := Real.sqrt_pos.mpr (mul_pos hℓ hV)
  have hs2 : Real.sqrt (ℓ * V) ^ 2 = ℓ * V := Real.sq_sqrt (mul_pos hℓ hV).le
  have hT0 : 0 ≤ |T| := abs_nonneg T
  have hT3 : |T| ^ 3 ≤ (z / Real.sqrt (ℓ * V)) ^ 3 := pow_le_pow_left₀ hT0 hT 3
  have key : ∀ s : ℝ, 0 < s → s^2 = ℓ * V →
      (ℓ * (C * V) / 6) * (z / s) ^ 3 = (C / 6) * z ^ 3 / s := by
    intro s hs hs2
    rw [show ℓ * (C * V) = C * (ℓ * V) by ring, ← hs2]
    field_simp
  have hCV : 0 ≤ ℓ * (C * V) / 6 := by
    have := mul_nonneg hℓ.le (mul_nonneg hC hV.le); linarith
  have hmid : (ℓ * M / 6) * |T| ^ 3 ≤ (C / 6) * z ^ 3 / Real.sqrt (ℓ * V) := by
    calc (ℓ * M / 6) * |T| ^ 3 ≤ (ℓ * (C * V) / 6) * |T| ^ 3 :=
          mul_le_mul_of_nonneg_right
            (div_le_div_of_nonneg_right (mul_le_mul_of_nonneg_left hM hℓ.le) (by norm_num))
            (pow_nonneg hT0 3)
      _ ≤ (ℓ * (C * V) / 6) * (z / Real.sqrt (ℓ * V)) ^ 3 := mul_le_mul_of_nonneg_left hT3 hCV
      _ = (C / 6) * z ^ 3 / Real.sqrt (ℓ * V) := key _ hs hs2
  have hden : Real.sqrt ℓ * Real.sqrt V₀ ≤ Real.sqrt (ℓ * V) := by
    rw [← Real.sqrt_mul hℓ.le]
    exact Real.sqrt_le_sqrt (mul_le_mul_of_nonneg_left hfloor hℓ.le)
  have hpos : 0 < Real.sqrt ℓ * Real.sqrt V₀ :=
    mul_pos (Real.sqrt_pos.mpr hℓ) (Real.sqrt_pos.mpr hV₀)
  calc _ ≤ _ := hmid
    _ ≤ _ := div_le_div_of_nonneg_left (by positivity) hpos hden

