-- Prove2me | solution 1 for Csg.idsCSG_bwInd_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T01:43:21.780479+00:00
-- url     : https://prove2.me/submissions/d7d5df9f-8009-4d31-a2bf-2d3ce601bf2d

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsCSG_bwInd_one
import Theorems.Thm_Csg_CSG_bwInd_succ
import Theorems.Thm_Csg_CSG_stageValue_mono


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (n : ℕ) (s : IDSState) :
    idsCSG.bwInd (fun _ => 0) n s ≤ idsCSG.bwInd (fun _ => 0) (n + 1) s := by
  induction n generalizing s with
  | zero =>
      have h0 : idsCSG.bwInd (fun _ => 0) 0 s = 0 := rfl
      rw [h0, idsCSG_bwInd_one s]
      cases s <;> norm_num [idsV1]
  | succ n ih =>
      rw [CSG.bwInd_succ, CSG.bwInd_succ]
      exact idsCSG.stageValue_mono ih
end Csg
