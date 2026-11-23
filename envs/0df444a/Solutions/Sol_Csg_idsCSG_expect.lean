-- Prove2me | solution 1 for Csg.idsCSG_expect
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:52:51.988279+00:00
-- url     : https://prove2.me/submissions/0756d0f4-ee16-4a28-90f2-1b6748ee9407

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) (a1 : PolicyAction) (a2 : AttackAction) (v : IDSState → ℝ) :
    idsCSG.expect s a1 a2 v = v (idsNext a1 a2) := by
  change ∑ s' : IDSState, (idsK s a1 a2 s').toReal * v s' = v (idsNext a1 a2)
  cases a1 <;> cases a2 <;> simp [idsK, idsNext, PMF.pure_apply, apply_ite ENNReal.toReal]
end Csg
