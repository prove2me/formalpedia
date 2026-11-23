-- Prove2me | solution 1 for Csg.idsP_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:51:21.705645+00:00
-- url     : https://prove2.me/submissions/934d31b3-dc63-49ff-a6fb-c702e90a0ce5

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_policyAction_sum
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : idsP ∈ stdSimplex ℝ PolicyAction :=
  ⟨fun a => by cases a <;> norm_num [idsP], by simp only [policyAction_sum, idsP]; norm_num⟩
end Csg
