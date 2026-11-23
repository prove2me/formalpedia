-- Prove2me | solution 1 for Csg.rpsCSG_untilOp_lfp_eq_reachOp_lfp
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:41:21.905158+00:00
-- url     : https://prove2.me/submissions/d4a24765-e478-4e42-b1b8-ccc989b7b378

import Definitions.Def_Csg_UntilOp
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsUntil
import Theorems.Thm_Csg_rpsCSG_untilOp_lfp_eq
import Theorems.Thm_Csg_rpsCSG_reachOp_lfp_eq


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero).lfp =
      (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp := by
  rw [rpsCSG_untilOp_lfp_eq, rpsCSG_reachOp_lfp_eq]
end Csg
