-- Prove2me | solution 1 for Freiman.middleRepair_frame_extend_proper
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:05.83689+00:00
-- url     : https://prove2.me/submissions/26283c35-92b9-4b5f-a415-087db3be77b5

import Theorems.Thm_Freiman_middleRepair_frame_normalize_physical
import Theorems.Thm_Freiman_middleRepair_frame_append_proper
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (s : MiddleRepairFrame) (u v : List ℕ+), middleDigits123 u → middleDigits123 v →
  0 < u.length+v.length → middleProper (middleRepairPhysical s)
    (middleRepairPhysical (middleRepairExtend s u v)) := by
  intro s u v hu hv hl
  simpa only [middleRepairExtend, middleRepair_frame_normalize_physical]
    using middleRepair_frame_append_proper (middleRepairNormalizeFrame s) u v hu hv hl
