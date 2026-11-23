-- Prove2me | solution 1 for Csg.rpsCSG_safetyOp_gfp_initial
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:42:30.645016+00:00
-- url     : https://prove2.me/submissions/532c947e-7ed5-4db0-9ca4-62c70166bff3

import Definitions.Def_Csg_SafetyCertificate
import Definitions.Def_Csg_RockPaperScissorsLfp
import Definitions.Def_Csg_RockPaperScissorsSafety
import Theorems.Thm_Csg_rpsCSG_safetyOp_gfp_eq
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_CSG_reachBounded_zero
attribute [local simp] Csg.CSG.bwInd_zero
attribute [local simp] Csg.CSG.reachBounded_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    ((rpsCSG.safetyOp rpsSafeUnresolved rpsR_zero).gfp RPSState.initial : ℝ) = 0 := by
  rw [rpsCSG_safetyOp_gfp_eq]
  simp [rpsVStarSafety]
end Csg
