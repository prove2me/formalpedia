-- Prove2me | solution 1 for Freiman.middleRepair_realized_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:05.796516+00:00
-- url     : https://prove2.me/submissions/3b5c383d-ba06-4432-8d2e-a4eb87a82ca2

import Theorems.Thm_Freiman_middleRepair_frame_realized_normalized
import Theorems.Thm_Freiman_middleRepair_frame_raw_child_proper
import Theorems.Thm_Freiman_middleRepair_frame_physical_realized_monotone
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c d : MiddleCore) (t : ℝ), middleRepairProper c d → middleRealized d t → middleRealized c t := by
  intro c d t hp hd
  obtain ⟨u,v,hu,hv,hl,rfl⟩ := hp
  have hr := middleRepair_frame_realized_normalized (middleRepairRawChild c u v) t hd
  have hc := middleRepair_frame_physical_realized_monotone (middleNormalized c)
    (middleRepairRawChild c u v) t (middleRepair_frame_raw_child_proper c u v hu hv hl) hr
  exact middleRepair_frame_realized_normalized c t hc
