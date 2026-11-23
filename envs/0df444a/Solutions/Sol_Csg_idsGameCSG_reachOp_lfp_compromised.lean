-- Prove2me | solution 1 for Csg.idsGameCSG_reachOp_lfp_compromised
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:28.561034+00:00
-- url     : https://prove2.me/submissions/98b284c0-079d-45fa-82e0-08d009fae172

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
import Theorems.Thm_Csg_idsGameCSG_reachOp_lfp_eq
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution :
    ((idsGameCSG.reachOp idsGoalHealthy idsGameCSG_r_zero).lfp .compromised : ℝ) = 1 := by
  rw [idsGameCSG_reachOp_lfp_eq]
  simp [idsVStar]
end Csg
