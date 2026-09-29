-- Prove2me | solution 1 for Freiman.middleRepair_frame_start_invariant
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:49.423479+00:00
-- url     : https://prove2.me/submissions/c8c8d8a3-828f-4875-90ff-3e391b7040b3

import Theorems.Thm_Freiman_middleRepair_frame_normalize_invariant
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ c : MiddleCore, middleRepairFrameInvariant (middleRepairStart c) := by
  intro c
  exact middleRepair_frame_normalize_invariant ⟨c,false⟩
