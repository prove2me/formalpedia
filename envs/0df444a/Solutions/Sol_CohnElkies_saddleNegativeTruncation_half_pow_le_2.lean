-- Prove2me | solution 2 for CohnElkies.saddleNegativeTruncation_half_pow_le
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:09:01.861006+00:00
-- url     : https://prove2.me/submissions/541b4b95-0db9-4e22-8370-b45f9b8b5ea6

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter Set MeasureTheory
open scoped Topology BigOperators


theorem solution (ℓ : ℝ) :
    (1 / 2 : ℝ) ^ saddleSmallResidueTruncation ℓ ≤
      2 * Real.exp (-10 * Real.log ℓ) := by
  unfold saddleSmallResidueTruncation
  have hn : 20 * Real.log ℓ ≤ ((⌈20 * Real.log ℓ⌉₊ : ℕ) : ℝ) := Nat.le_ceil _
  have hn0 : (0:ℝ) ≤ ((⌈20 * Real.log ℓ⌉₊ : ℕ) : ℝ) := Nat.cast_nonneg _
  have hl2 := Real.log_two_gt_d9
  rw [← Real.rpow_natCast, Real.rpow_def_of_pos (by norm_num), one_div, Real.log_inv]
  have : Real.exp (-Real.log 2 * ((⌈20 * Real.log ℓ⌉₊ : ℕ) : ℝ)) ≤ Real.exp (-10 * Real.log ℓ) := by
    apply Real.exp_le_exp.2
    rcases le_total 0 (Real.log ℓ) with h | h <;> nlinarith
  linarith [Real.exp_pos (-10 * Real.log ℓ)]

