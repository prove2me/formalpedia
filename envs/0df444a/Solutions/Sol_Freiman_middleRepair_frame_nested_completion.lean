-- Prove2me | solution 1 for Freiman.middleRepair_frame_nested_completion
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:22.410545+00:00
-- url     : https://prove2.me/submissions/1c3389d7-b10e-4aee-aa2c-4e5dd1ff108c

import Theorems.Thm_Freiman_middleRepair_frame_path_physical
import Theorems.Thm_Freiman_middleRepair_frame_prefix_completion
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c : MiddleCore) (t : ℝ) (s : ℕ → MiddleRepairFrame), middleRepairFramePath c t s →
  ∃ a : ℤ → ℕ+, ∀ n : ℕ, middleCompatible (middleRepairPhysical (s n)) a := by
  intro c t s hs
  exact middleRepair_frame_prefix_completion (fun n => middleRepairPhysical (s n))
    (middleRepair_frame_path_physical c t s hs).2
