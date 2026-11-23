-- Prove2me | solution 1 for Csg.idsUnifP_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:56:31.648305+00:00
-- url     : https://prove2.me/submissions/e8089239-90f2-4709-84a4-61c14e9c6562

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_policyAction_sum
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : idsUnifP ∈ stdSimplex ℝ PolicyAction :=
  ⟨fun a => by cases a <;> norm_num [idsUnifP], by simp only [policyAction_sum, idsUnifP]; norm_num⟩
end Csg
