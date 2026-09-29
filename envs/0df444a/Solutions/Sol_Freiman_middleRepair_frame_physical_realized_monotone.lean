-- Prove2me | solution 1 for Freiman.middleRepair_frame_physical_realized_monotone
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:05.661206+00:00
-- url     : https://prove2.me/submissions/feebea4b-f7c5-491a-99df-116dfca24c37

import Theorems.Thm_Freiman_middle_compatible_monotone
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c d : MiddleCore) (t : ℝ), middleProper c d → middleRealized d t → middleRealized c t := by
  intro c d t hp hd
  obtain ⟨a,ha,ht⟩ := hd
  exact ⟨a,middle_compatible_monotone c d a hp ha,ht⟩
