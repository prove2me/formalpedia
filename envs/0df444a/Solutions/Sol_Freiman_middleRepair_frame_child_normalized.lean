-- Prove2me | solution 1 for Freiman.middleRepair_frame_child_normalized
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:49.389913+00:00
-- url     : https://prove2.me/submissions/8bc7ef1a-25ad-4448-aed7-692df49c7f3e

import Theorems.Thm_Freiman_middleRepair_frame_normalized_idem
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c : MiddleCore) (u v : List ℕ+),
  middleRepairChild (middleNormalized c) u v = middleRepairChild c u v := by
  intro c u v
  simp only [middleRepairChild, middleRepairRawChild, middleRepair_frame_normalized_idem]
