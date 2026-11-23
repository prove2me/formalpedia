-- Prove2me | solution 1 for Csg.rpsCSG_reachOp_lfp_initial_mem_Icc
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:42:48.7778+00:00
-- url     : https://prove2.me/submissions/834fd450-c549-4bff-8d75-b0426a2337dc

import Definitions.Def_Csg_IntervalCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsInterval
import Theorems.Thm_Csg_rpsCSG_reachOp_lfp_mem_Icc

set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    (1 : ℝ) / 3 ≤ ((rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) ∧
      ((rpsCSG.reachOp rpsGoalWin2 rpsR_zero).lfp RPSState.initial : ℝ) ≤ 2 / 3 :=
  ⟨rpsCSG_reachOp_lfp_mem_Icc.1 RPSState.initial, rpsCSG_reachOp_lfp_mem_Icc.2 RPSState.initial⟩
end Csg
