-- Prove2me | solution 2 for Freiman.middleRepair_path_realized
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-10T17:09:26.826031+00:00
-- url     : https://prove2.me/submissions/e80a14d6-7efd-4242-9c71-7afebfcd1da6

import Theorems.Thm_Freiman_middleRepair_frame_path_lift
import Theorems.Thm_Freiman_middleRepair_frame_path_realized
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c : MiddleCore) (t : ℝ) (p : ℕ → MiddleCore), middleRepairPath c t p → middleRealized c t := by
  intro c t p hp
  obtain ⟨s,hs⟩ := middleRepair_frame_path_lift c t p hp
  exact middleRepair_frame_path_realized c t p s hp hs
