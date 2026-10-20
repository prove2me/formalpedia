-- Prove2me | solution 2 for CohnElkies.lowerWallisPhaseKernel_abs_le_tail
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:27:33.390864+00:00
-- url     : https://prove2.me/submissions/5704e595-3c3c-4f78-8273-e69322042660

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Filter MeasureTheory Set
open scoped Interval Topology


theorem solution
    (u : ℝ) {t : ℝ} (ht : 1 ≤ t) :
    |lowerWallisPhaseKernel u t| ≤
      1 / t ^ 2 + Real.exp (-t) := by
  unfold lowerWallisPhaseKernel
  have ht0 : 0 < t := by linarith
  have he : 0 < Real.exp (-t) := Real.exp_pos _
  have he1 : Real.exp (-t) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  have ht2 : 0 < t ^ 2 := by positivity
  rw [abs_div, abs_of_pos ht2, div_le_iff₀ ht2]
  have hc := Real.abs_cos_le_one (u * t)
  have h1 : |(1 - Real.exp (-t)) * Real.cos (u * t) - t * Real.exp (-t)| ≤ 1 + t * Real.exp (-t) := by
    calc _ ≤ |(1 - Real.exp (-t)) * Real.cos (u * t)| + |t * Real.exp (-t)| := abs_sub _ _
      _ = (1 - Real.exp (-t)) * |Real.cos (u * t)| + t * Real.exp (-t) := by
          rw [abs_mul, abs_of_nonneg (by linarith), abs_of_pos (mul_pos ht0 he)]
      _ ≤ 1 + t * Real.exp (-t) := by nlinarith
  have h2 : (1 / t ^ 2 + Real.exp (-t)) * t ^ 2 = 1 + t ^ 2 * Real.exp (-t) := by
    field_simp
  rw [h2]
  nlinarith [mul_le_mul_of_nonneg_right (show t ≤ t^2 by nlinarith) he.le]

