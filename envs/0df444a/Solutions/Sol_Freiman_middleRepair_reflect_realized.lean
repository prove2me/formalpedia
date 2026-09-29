-- Prove2me | solution 1 for Freiman.middleRepair_reflect_realized
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:33.69537+00:00
-- url     : https://prove2.me/submissions/e2d31d62-633c-4c2e-8ebf-39e7db250a0a

import Theorems.Thm_Freiman_middleRepair_frame_compatible_core
import Theorems.Thm_Freiman_middleRepair_reflect_act_localValue
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (b : Bool) (c : MiddleCore) (t : ℝ), middleRealized (middleRepairAct b c) t → middleRealized c t := by
  intro b c t h
  obtain ⟨a,ha,ht⟩ := h
  refine ⟨middleRepairActDigits b a, ?_, ?_⟩
  · exact middleRepair_frame_compatible_core ⟨c,b⟩ a ha
  · rw [middleRepair_reflect_act_localValue]
    exact ht
