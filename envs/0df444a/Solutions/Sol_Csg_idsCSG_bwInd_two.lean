-- Prove2me | solution 1 for Csg.idsCSG_bwInd_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:00:30.249848+00:00
-- url     : https://prove2.me/submissions/0a918cb2-c999-4ecf-9199-107e0d4f3c0f

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsCSG_bwInd_one
import Theorems.Thm_Csg_idsCSG_stageValue_two
import Theorems.Thm_Csg_CSG_bwInd_succ


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) : idsCSG.bwInd (fun _ => 0) 2 s = idsV2 s := by
  rw [CSG.bwInd_succ]
  rw [show idsCSG.bwInd (fun _ => 0) 1 = idsV1 from funext idsCSG_bwInd_one]
  exact idsCSG_stageValue_two s
end Csg
