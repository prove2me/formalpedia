-- Prove2me | solution 1 for Freiman.middleRepair_path_choice
-- status  : ACCEPTED   (prove)
-- author  : @tp
-- created : 2026-09-09T15:27:06.077953+00:00
-- url     : https://prove2.me/submissions/6a41d93b-f798-47aa-9378-e2513f0c7b85

import Theorems.Thm_Freiman_middleRepair_frame_path_choice_normalized
import Theorems.Thm_Freiman_middleRepair_frame_normalized_idem
import Theorems.Thm_Freiman_middleRepair_frame_normalized_regular
import Theorems.Thm_Freiman_middleRepair_frame_normalized_good
import Theorems.Thm_Freiman_middleRepair_frame_normalized_cover
import Theorems.Thm_Freiman_middleRepair_frame_realized_normalized
import Mathlib.Tactic

open Freiman

theorem solution :
  (∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → t∈middleCover c →
  middleRealized c t ∨ ∃ d : MiddleCore, middleRegular d ∧ middleRepairGood d ∧ middleRepairProper c d ∧ t∈middleCover d) →
  (∀ (c d : MiddleCore) (t : ℝ), middleRepairProper c d → middleRealized d t → middleRealized c t) →
  ∀ (c : MiddleCore) (t : ℝ), middleRegular c → middleRepairGood c → t∈middleCover c →
    middleRealized c t ∨ ∃ p : ℕ → MiddleCore, middleRepairPath c t p := by
  intro hs hm c t hc hg ht
  have hct : t∈middleCover (middleNormalized c) := by
    simpa only [middleRepair_frame_normalized_cover] using ht
  rcases middleRepair_frame_path_choice_normalized hs hm (middleNormalized c) t
    (middleRepair_frame_normalized_idem c) (middleRepair_frame_normalized_regular c hc)
    ((middleRepair_frame_normalized_good c).mpr hg) hct with h | ⟨p,hp⟩
  · exact Or.inl (middleRepair_frame_realized_normalized c t h)
  · right
    refine ⟨p,?_,hp.2⟩
    simpa only [middleRepair_frame_normalized_idem] using hp.1
