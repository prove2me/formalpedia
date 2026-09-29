-- Prove2me | solution 1 for Freiman.middleRepair_frame_oscillation
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:22.360752+00:00
-- url     : https://prove2.me/submissions/715247da-9c17-45a8-891d-d6848d4698d8

import Theorems.Thm_Freiman_middleRepair_frame_compatible_core
import Theorems.Thm_Freiman_middleRepair_reflect_act_localValue
import Theorems.Thm_Freiman_middle_compatible_oscillation
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (s : MiddleRepairFrame) (a : ℤ → ℕ+) (t : ℝ), middleRegular s.core →
  middleCompatible (middleRepairPhysical s) a → t∈middleCover s.core →
    |localValue a 0-t| ≤ middleWidth s.core.left+middleWidth s.core.right := by
  intro s a t hr hc ht
  have hb := middle_compatible_oscillation s.core (middleRepairActDigits s.reflected a) t hr
    (middleRepair_frame_compatible_core s a hc) ht
  simpa only [middleRepair_reflect_act_localValue] using hb
