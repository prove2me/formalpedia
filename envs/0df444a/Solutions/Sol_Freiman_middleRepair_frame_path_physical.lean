-- Prove2me | solution 1 for Freiman.middleRepair_frame_path_physical
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:22.250896+00:00
-- url     : https://prove2.me/submissions/42393dc8-cc5b-4a9d-8467-e945093604fa

import Theorems.Thm_Freiman_middleRepair_frame_start_physical
import Theorems.Thm_Freiman_middleRepair_frame_extend_proper
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c : MiddleCore) (t : ℝ) (s : ℕ → MiddleRepairFrame), middleRepairFramePath c t s →
  middleRepairPhysicalPath c s := by
  intro c t s hs
  refine ⟨?_,?_⟩
  · rw [hs.1]
    exact middleRepair_frame_start_physical c
  · intro n
    obtain ⟨u,v,hu,hv,hl,he⟩ := (hs.2 n).2.2.2.2
    rw [he]
    exact middleRepair_frame_extend_proper (s n) u v hu hv hl
