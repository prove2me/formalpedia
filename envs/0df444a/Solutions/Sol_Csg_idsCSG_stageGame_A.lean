-- Prove2me | solution 1 for Csg.idsCSG_stageGame_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:19:21.291584+00:00
-- url     : https://prove2.me/submissions/de755f95-0b62-4899-8d92-19576de194d1

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction) :
    (idsCSG.stageGame s (fun _ => 0)).A a1 a2 = idsR s a1 a2 := by
  have hexpect : idsCSG.expect s a1 a2 (fun _ => 0) = 0 := by
    unfold CSG.expect
    simp
  change idsCSG.r s a1 a2 + idsCSG.expect s a1 a2 (fun _ => 0) = idsR s a1 a2
  rw [hexpect, add_zero]
  rfl
end Csg
