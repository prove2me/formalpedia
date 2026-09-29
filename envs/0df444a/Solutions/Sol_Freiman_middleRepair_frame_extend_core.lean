-- Prove2me | solution 1 for Freiman.middleRepair_frame_extend_core
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:05.944053+00:00
-- url     : https://prove2.me/submissions/6167c909-4c75-46ea-ad33-549c52a80b7f

import Theorems.Thm_Freiman_middleRepair_frame_normalize_core
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (s : MiddleRepairFrame) (u v : List ℕ+),
  (middleRepairExtend s u v).core = middleRepairChild s.core u v := by
  intro s u v
  simp only [middleRepairExtend, middleRepair_frame_normalize_core,
    middleRepairChild, middleRepairRawChild]
