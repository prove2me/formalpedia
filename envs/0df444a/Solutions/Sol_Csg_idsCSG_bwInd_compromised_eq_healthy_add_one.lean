-- Prove2me | solution 1 for Csg.idsCSG_bwInd_compromised_eq_healthy_add_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:14.314197+00:00
-- url     : https://prove2.me/submissions/ec01f302-9fbb-4486-bbdb-d8e0750c6330

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsCSG_stageValue_compromised_eq_healthy_add_one
import Theorems.Thm_Csg_CSG_bwInd_succ


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (n : ℕ) :
    idsCSG.bwInd (fun _ => 0) (n + 1) .compromised =
      idsCSG.bwInd (fun _ => 0) (n + 1) .healthy + 1 := by
  rw [CSG.bwInd_succ, CSG.bwInd_succ]
  exact idsCSG_stageValue_compromised_eq_healthy_add_one _
end Csg
