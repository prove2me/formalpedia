-- Prove2me | solution 1 for DeletionCode.RedundancyBounds.labelCount_positive
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:17:17.721661+00:00
-- url     : https://prove2.me/submissions/89a6afd7-67a7-44b9-9154-d6bb1493f990

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds
import Theorems.Thm_DeletionCode_PaperParameters_nine_le_L


set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery
namespace DeletionCode.RedundancyBounds
theorem _root_.solution (t n : ℕ) (hn : 1 ≤ n) : 0 < labelCount t n := by
  have hL : 0 < PaperParameters.L n := by have := PaperParameters.nine_le_L n; omega
  unfold labelCount
  exact mul_pos (mul_pos (by decide : 0 < 8) (pow_pos (by omega) _)) (pow_pos hL _)
end DeletionCode.RedundancyBounds
