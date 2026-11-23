-- Prove2me | solution 1 for Csg.idsCSG_stageGame_compromised_eq_healthy_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:56:57.341607+00:00
-- url     : https://prove2.me/submissions/997e1267-0766-4d3b-9c29-d1acdd7d06e6

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_P2M_Csg_idsCSG_stageGame_A__7bb1bc444f1d
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (v : IDSState → ℝ) (a1 : PolicyAction)
    (a2 : AttackAction) :
    (idsCSG.stageGame .compromised v).A a1 a2 = (idsCSG.stageGame .healthy v).A a1 a2 + 1 := by
  rw [idsCSG_stageGame_A', idsCSG_stageGame_A']
  cases a1 <;> cases a2 <;> simp [idsR] <;> ring
end Csg
