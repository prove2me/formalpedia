-- Prove2me | solution 1 for Freiman.middleRepair_frame_normalized_cover
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:49.626992+00:00
-- url     : https://prove2.me/submissions/5cb5d062-3261-4d58-90f2-2decf240ddfe

import Theorems.Thm_Freiman_middleRepair_frame_normalized_idem
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ c : MiddleCore, middleCover (middleNormalized c) = middleCover c := by
  intro c
  simp only [middleCover, middleBounds, middleRepair_frame_normalized_idem]
