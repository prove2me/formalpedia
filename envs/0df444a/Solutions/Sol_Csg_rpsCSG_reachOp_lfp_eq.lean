-- Prove2me | solution 1 for Csg.rpsCSG_reachOp_lfp_eq
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:47:48.447305+00:00
-- url     : https://prove2.me/submissions/f15619cf-9af8-4ef1-9341-683d943ce579

import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_RockPaperScissors
import Definitions.Def_Csg_RockPaperScissorsLfp
import Theorems.Thm_Csg_rpsVStar_fixed
import Theorems.Thm_Csg_rpsVStar_le_of_prefixed
import Theorems.Thm_Csg_CSG_reachOp_lfp_eq_of_certificate


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp = rpsVStar :=
  rpsCSG.reachOp_lfp_eq_of_certificate rpsGoalWin2 rpsR_zero rpsVStar rpsVStar_fixed
    fun _ hb => rpsVStar_le_of_prefixed hb
end Csg
