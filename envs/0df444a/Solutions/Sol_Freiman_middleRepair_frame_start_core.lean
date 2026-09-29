-- Prove2me | solution 1 for Freiman.middleRepair_frame_start_core
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:49.56546+00:00
-- url     : https://prove2.me/submissions/a5df6c73-c8d0-4544-bc56-8e11eb687ee7

import Theorems.Thm_Freiman_middleRepair_frame_normalize_core
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ c : MiddleCore, (middleRepairStart c).core = middleNormalized c := by
  intro c
  exact middleRepair_frame_normalize_core ⟨c,false⟩
