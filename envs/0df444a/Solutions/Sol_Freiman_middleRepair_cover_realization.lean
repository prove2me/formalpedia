-- Prove2me | solution 1 for Freiman.middleRepair_cover_realization
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:37.806464+00:00
-- url     : https://prove2.me/submissions/d17384f3-023f-408d-99a7-161f93c9bd30

import Theorems.Thm_Freiman_middleRepair_path_choice
import Theorems.Thm_Freiman_middleRepair_step
import Theorems.Thm_Freiman_middleRepair_realized_monotone
import Theorems.Thm_Freiman_middleRepair_path_realized
import Mathlib.Tactic

open Freiman

theorem solution :
  ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → t∈middleCover c → middleRealized c t := by
  intro c t hc hg ht
  rcases middleRepair_path_choice middleRepair_step middleRepair_realized_monotone c t hc hg ht with h | ⟨p,hp⟩
  · exact h
  · exact middleRepair_path_realized c t p hp
