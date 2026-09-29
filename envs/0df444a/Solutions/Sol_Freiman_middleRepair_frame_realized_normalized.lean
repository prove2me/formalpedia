-- Prove2me | solution 1 for Freiman.middleRepair_frame_realized_normalized
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:32.555421+00:00
-- url     : https://prove2.me/submissions/0fb8095f-7df6-4518-b96d-de6d80bcd1c9

import Theorems.Thm_Freiman_middleRepair_reflect_realized
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c : MiddleCore) (t : ℝ), middleRealized (middleNormalized c) t → middleRealized c t := by
  intro c t ht
  by_cases h : middleWidth c.right ≤ middleWidth c.left
  · simpa only [middleNormalized, if_pos h] using ht
  · apply middleRepair_reflect_realized true c t
    simpa only [middleNormalized, if_neg h, middleRepairAct, middleRepairSwap, ↓reduceIte] using ht
