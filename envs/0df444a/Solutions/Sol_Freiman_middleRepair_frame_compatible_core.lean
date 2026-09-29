-- Prove2me | solution 1 for Freiman.middleRepair_frame_compatible_core
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:32.276994+00:00
-- url     : https://prove2.me/submissions/d3158611-046e-4284-ab44-8b18fdfb4d27

import Theorems.Thm_Freiman_middleRepair_reflect_compatible
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (s : MiddleRepairFrame) (a : ℤ → ℕ+), middleCompatible (middleRepairPhysical s) a →
  middleCompatible s.core (middleRepairActDigits s.reflected a) := by
  intro s a ha
  rcases s with ⟨c,b⟩
  cases b with
  | false => exact ha
  | true =>
    have h := middleRepair_reflect_compatible (middleRepairSwap c) a ha
    simpa only [middleRepairPhysical, middleRepairAct, middleRepairActDigits,
      middleRepairSwap, Bool.true_eq, ↓reduceIte] using h
