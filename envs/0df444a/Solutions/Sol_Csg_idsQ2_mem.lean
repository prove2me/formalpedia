-- Prove2me | solution 1 for Csg.idsQ2_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:54:56.73693+00:00
-- url     : https://prove2.me/submissions/3c11aeae-9acd-4ce9-a101-427a37a271d9

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_attackAction_sum
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution : idsQ2 ∈ stdSimplex ℝ AttackAction :=
  ⟨fun a => by cases a <;> norm_num [idsQ2], by simp only [attackAction_sum, idsQ2]; norm_num⟩
end Csg
