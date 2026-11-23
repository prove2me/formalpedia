-- Prove2me | solution 1 for Csg.rpsCSG_untilOp_lfp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:48:39.718195+00:00
-- url     : https://prove2.me/submissions/19a4fc4b-64d9-4dfe-906c-c9327125ffb5

import Definitions.Def_Csg_UntilOp
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsUntil
import Theorems.Thm_Csg_rpsVStar_fixed_until
import Theorems.Thm_Csg_rpsVStar_le_of_prefixed_until
import Theorems.Thm_OrderHom_lfp_eq_of_certificate


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero).lfp = rpsVStar :=
  OrderHom.lfp_eq_of_certificate (rpsCSG.untilOp rpsSafeNotWin1 rpsGoalWin2 rpsR_zero) rpsVStar
    rpsVStar_fixed_until fun _ hb => rpsVStar_le_of_prefixed_until hb
end Csg
