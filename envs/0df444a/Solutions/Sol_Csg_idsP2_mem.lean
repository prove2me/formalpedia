-- Prove2me | solution 1 for Csg.idsP2_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:54:00.500343+00:00
-- url     : https://prove2.me/submissions/aed9a8eb-59b8-4721-960f-a63e27312449

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
theorem _root_.solution : idsP2 ∈ stdSimplex ℝ PolicyAction :=
  ⟨fun a => by cases a <;> norm_num [idsP2], by simp only [policyAction_sum, idsP2]; norm_num⟩
end Csg
