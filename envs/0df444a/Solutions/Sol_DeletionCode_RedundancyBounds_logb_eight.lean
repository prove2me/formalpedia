-- Prove2me | solution 1 for DeletionCode.RedundancyBounds.logb_eight
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T05:48:43.086208+00:00
-- url     : https://prove2.me/submissions/69e40f39-a96c-4df0-8caf-d37f0d703de7

import Definitions.Def_DeletionCode_PaperParameters
import Definitions.Def_DeletionCode_WitnessCost
import Definitions.Def_DeletionCode_RedundancyBounds

set_option autoImplicit true
open DeletionCode DeletionCode.RedundancyBounds
open HeaderRecovery
namespace DeletionCode.RedundancyBounds
theorem _root_.solution : Real.logb 2 (8 : ℝ) = 3 := by
  calc
    Real.logb 2 (8 : ℝ) = Real.logb 2 ((2 : ℝ) ^ (3 : ℕ)) := by norm_num
    _ = 3 := by
      rw [Real.logb_pow, Real.logb_self_eq_one (by norm_num : (1 : ℝ) < 2)]
      norm_num
end DeletionCode.RedundancyBounds
