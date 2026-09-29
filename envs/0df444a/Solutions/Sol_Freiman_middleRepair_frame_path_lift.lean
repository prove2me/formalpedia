-- Prove2me | solution 1 for Freiman.middleRepair_frame_path_lift
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:22.252584+00:00
-- url     : https://prove2.me/submissions/b4719507-89a0-4913-bf41-ed6294dd6f88

import Theorems.Thm_Freiman_middleRepair_frame_path_labels
import Theorems.Thm_Freiman_middleRepair_frame_path_build
import Theorems.Thm_Freiman_middleRepair_frame_start_core
import Theorems.Thm_Freiman_middleRepair_frame_start_invariant
import Theorems.Thm_Freiman_middleRepair_frame_extend_core
import Theorems.Thm_Freiman_middleRepair_frame_extend_invariant
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c : MiddleCore) (t : ℝ) (p : ℕ → MiddleCore), middleRepairPath c t p →
  ∃ s : ℕ → MiddleRepairFrame, middleRepairLift c t p s := by
  intro c t p hp
  obtain ⟨u,v,huv⟩ := middleRepair_frame_path_labels c t p hp
  exact middleRepair_frame_path_build middleRepair_frame_start_core middleRepair_frame_start_invariant
    middleRepair_frame_extend_core middleRepair_frame_extend_invariant c t p u v hp huv
