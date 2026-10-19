-- Prove2me | solution 2 for CohnElkies.saddleSmallResidueTruncation_half_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:23:29.50699+00:00
-- url     : https://prove2.me/submissions/e2051079-901b-41b3-9b4b-090361526c57

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


theorem solution
    (ℓ : ℝ) :
    (1 / 2 : ℝ) ^
        (saddleSmallResidueTruncation ℓ + 1) ≤
      Real.exp (-10 * Real.log ℓ) := by
  have hpow : (1/2:ℝ)^(saddleSmallResidueTruncation ℓ + 1) =
      Real.exp (-(((saddleSmallResidueTruncation ℓ + 1 : ℕ) : ℝ) * Real.log 2)) := by
    rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num)]
    congr 1; rw [one_div, Real.log_inv]; ring
  rw [hpow, Real.exp_le_exp]
  have hc : 20 * Real.log ℓ ≤ (saddleSmallResidueTruncation ℓ : ℝ) := Nat.le_ceil _
  have hl2 := Real.log_two_gt_d9
  have hn : (0:ℝ) ≤ saddleSmallResidueTruncation ℓ := Nat.cast_nonneg _
  push_cast
  rcases le_total (Real.log ℓ) 0 with hL | hL
  · nlinarith
  · nlinarith

