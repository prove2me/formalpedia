-- Prove2me | solution 1 for Freiman.middleRepair_frame_start_physical
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:26:49.601413+00:00
-- url     : https://prove2.me/submissions/bd0995db-dfbb-40b1-98ef-422159d261f2

import Theorems.Thm_Freiman_middleRepair_frame_normalize_physical
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ c : MiddleCore, middleRepairPhysical (middleRepairStart c) = c := by
  intro c
  exact middleRepair_frame_normalize_physical ⟨c,false⟩
