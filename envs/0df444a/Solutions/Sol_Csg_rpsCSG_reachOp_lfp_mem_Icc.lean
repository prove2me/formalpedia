-- Prove2me | solution 1 for Csg.rpsCSG_reachOp_lfp_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:52:23.44294+00:00
-- url     : https://prove2.me/submissions/1f36d38d-6b2a-4bf0-96e1-a6d93b8d5a87

import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsInterval
import Theorems.Thm_Csg_rpsLo_le_of_prefixed
import Theorems.Thm_Csg_rpsHi_prefixed
import Theorems.Thm_Csg_CSG_reachOp_lfp_mem_Icc_of_certificate


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    rpsLo ≤ (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp ∧
      (rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp ≤ rpsHi :=
  rpsCSG.reachOp_lfp_mem_Icc_of_certificate rpsGoalWin2 rpsR_zero rpsLo rpsHi
    (fun _ hb => rpsLo_le_of_prefixed hb) rpsHi_prefixed
end Csg
