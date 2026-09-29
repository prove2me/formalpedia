-- Prove2me | solution 1 for Freiman.middleRepair_frame_extend_invariant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:05.747058+00:00
-- url     : https://prove2.me/submissions/b360958e-5420-4181-9f01-710ac357b4ec

import Theorems.Thm_Freiman_middleRepair_frame_normalize_invariant
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (s : MiddleRepairFrame) (u v : List ℕ+),
  middleRepairFrameInvariant (middleRepairExtend s u v) := by
  intro s u v
  exact middleRepair_frame_normalize_invariant _
