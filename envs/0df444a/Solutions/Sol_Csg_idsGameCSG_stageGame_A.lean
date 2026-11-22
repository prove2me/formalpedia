-- Prove2me | solution 1 for Csg.idsGameCSG_stageGame_A
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T22:53:10.098807+00:00
-- url     : https://prove2.me/submissions/75b22d14-19bd-4d4f-8450-7d6cab8c6a41

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction)
    (v : IDSState → ℝ) :
    (idsGameCSG.stageGame s v).A a1 a2 = v (idsNext a1 a2) := by
  have hexpect : idsGameCSG.expect s a1 a2 v = v (idsNext a1 a2) := by
    change ∑ s' : IDSState, (idsK s a1 a2 s').toReal * v s' = v (idsNext a1 a2)
    cases a1 <;> cases a2 <;> simp [idsK, idsNext, PMF.pure_apply, apply_ite ENNReal.toReal]
  change idsGameCSG.r s a1 a2 + idsGameCSG.expect s a1 a2 v = v (idsNext a1 a2)
  rw [hexpect, idsGameCSG_r_zero s a1 a2, zero_add]
end Csg
