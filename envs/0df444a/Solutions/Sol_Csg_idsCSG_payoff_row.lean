-- Prove2me | solution 1 for Csg.idsCSG_payoff_row
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:51:53.071942+00:00
-- url     : https://prove2.me/submissions/ced958b6-7ea7-4c7b-b698-6c9ab5ab4885

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_attackAction_sum
import Theorems.Thm_Csg_idsCSG_stageGame_A
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) {p' : PolicyAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ PolicyAction) :
    (idsCSG.stageGame s (fun _ => 0)).payoff p' idsQ = idsV1 s := by
  have hinner : ∀ a1, ∑ a2, (idsCSG.stageGame s (fun _ => 0)).A a1 a2 * idsQ a2 = idsV1 s := by
    intro a1
    rw [attackAction_sum]
    cases s <;> cases a1 <;> simp [idsCSG_stageGame_A, idsR, idsQ, idsV1] <;> norm_num
  rw [MatrixGame.payoff_eq_sum_mul]
  calc ∑ a1, p' a1 * ∑ a2, (idsCSG.stageGame s (fun _ => 0)).A a1 a2 * idsQ a2
      = ∑ a1, p' a1 * idsV1 s := Finset.sum_congr rfl fun a1 _ => by rw [hinner a1]
    _ = (∑ a1, p' a1) * idsV1 s := by rw [← Finset.sum_mul]
    _ = idsV1 s := by rw [hp'.2, one_mul]
end Csg
