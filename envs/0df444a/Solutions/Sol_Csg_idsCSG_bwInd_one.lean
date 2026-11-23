-- Prove2me | solution 1 for Csg.idsCSG_bwInd_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:56:25.0552+00:00
-- url     : https://prove2.me/submissions/2042f1ae-382f-4940-912b-e1a482699ef7

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsCSG_stageValue
import Theorems.Thm_Csg_CSG_bwInd_succ
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) : idsCSG.bwInd (fun _ => 0) 1 s = idsV1 s := by
  rw [CSG.bwInd_succ, CSG.bwInd_zero]
  exact idsCSG_stageValue s
end Csg
