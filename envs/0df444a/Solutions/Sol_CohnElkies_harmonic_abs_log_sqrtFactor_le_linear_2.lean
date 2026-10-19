-- Prove2me | solution 2 for CohnElkies.harmonic_abs_log_sqrtFactor_le_linear
-- status  : ACCEPTED   (prove)
-- author  : @fizzyinc3
-- created : 2026-10-19T12:22:06.806841+00:00
-- url     : https://prove2.me/submissions/f0454345-d2f7-4005-a9da-65a5f0112f10

import Mathlib
import Definitions.Def_SpherePacking
set_option autoImplicit true
open CohnElkies
set_option backward.isDefEq.respectTransparency false
set_option backward.defeqAttrib.useBackward true
set_option maxHeartbeats 800000
noncomputable section
open Asymptotics Bornology Complex Filter Function MeasureTheory Metric Set
open scoped Filter FourierTransform Real SchwartzMap Topology


theorem solution
    {c x : ℝ} (hc : 0 ≤ c) (hx : 2 ≤ x) :
    |Real.log
      (Real.sqrt (c ^ 2 + (x / 2) ^ 2))| ≤ c + x := by
  have hs1 : 1 ≤ Real.sqrt (c ^ 2 + (x / 2) ^ 2) := by
    rw [Real.le_sqrt (by norm_num) (by positivity)]; nlinarith
  have hs2 : Real.sqrt (c ^ 2 + (x / 2) ^ 2) ≤ c + x := by
    rw [Real.sqrt_le_left (by linarith)]; nlinarith
  have hlog0 : 0 ≤ Real.log (Real.sqrt (c ^ 2 + (x / 2) ^ 2)) := Real.log_nonneg hs1
  have hlog1 := Real.log_le_sub_one_of_pos (by linarith : 0 < Real.sqrt (c ^ 2 + (x / 2) ^ 2))
  rw [abs_of_nonneg hlog0]
  linarith

