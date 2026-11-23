-- Prove2me | solution 1 for Csg.idsUnifQ_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:56:34.718813+00:00
-- url     : https://prove2.me/submissions/af7d7f54-e74b-424b-8d6e-b4617ff15e1f

import Definitions.Def_Csg_IntrusionDetection
import Definitions.Def_Csg_ReachCertificate
import Definitions.Def_Csg_IntrusionDetectionReach
import Theorems.Thm_Csg_CSG_bwInd_zero
import Theorems.Thm_Csg_attackAction_sum
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : idsUnifQ ∈ stdSimplex ℝ AttackAction :=
  ⟨fun a => by cases a <;> norm_num [idsUnifQ], by simp only [attackAction_sum, idsUnifQ]; norm_num⟩
end Csg
