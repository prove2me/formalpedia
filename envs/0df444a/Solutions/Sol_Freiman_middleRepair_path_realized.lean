-- Prove2me | solution 1 for Freiman.middleRepair_path_realized
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:37.810978+00:00
-- url     : https://prove2.me/submissions/7c84b865-383e-4546-b874-26686bd2751f

import Theorems.Thm_Freiman_middleRepair_frame_path_lift
import Theorems.Thm_Freiman_middleRepair_frame_path_realized
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c : MiddleCore) (t : ℝ) (p : ℕ → MiddleCore), middleRepairPath c t p → middleRealized c t := by
  intro c t p hp
  obtain ⟨s,hs⟩ := middleRepair_frame_path_lift c t p hp
  exact middleRepair_frame_path_realized c t p s hp hs
