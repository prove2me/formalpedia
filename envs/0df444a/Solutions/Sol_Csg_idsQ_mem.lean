-- Prove2me | solution 1 for Csg.idsQ_mem
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:51:43.626446+00:00
-- url     : https://prove2.me/submissions/88d18b24-cfc9-4e5d-a102-fa93f615610a

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
theorem _root_.solution : idsQ ∈ stdSimplex ℝ AttackAction :=
  ⟨fun a => by cases a <;> norm_num [idsQ], by simp only [attackAction_sum, idsQ]; norm_num⟩
end Csg
