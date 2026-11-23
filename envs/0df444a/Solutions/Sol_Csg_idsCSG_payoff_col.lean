-- Prove2me | solution 1 for Csg.idsCSG_payoff_col
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:52:04.057822+00:00
-- url     : https://prove2.me/submissions/57529c18-95cb-4ae9-a0d2-3b00474dade8

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_policyAction_sum
import Theorems.Thm_Csg_idsCSG_stageGame_A
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) {q' : AttackAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ AttackAction) :
    (idsCSG.stageGame s (fun _ => 0)).payoff idsP q' = idsV1 s := by
  have hinner : ∀ a2, ∑ a1, idsP a1 * (idsCSG.stageGame s (fun _ => 0)).A a1 a2 = idsV1 s := by
    intro a2
    rw [policyAction_sum]
    cases s <;> cases a2 <;> simp [idsCSG_stageGame_A, idsR, idsP, idsV1] <;> norm_num
  rw [MatrixGame.payoff_eq_sum_mul']
  calc ∑ a2, (∑ a1, idsP a1 * (idsCSG.stageGame s (fun _ => 0)).A a1 a2) * q' a2
      = ∑ a2, idsV1 s * q' a2 := Finset.sum_congr rfl fun a2 _ => by rw [hinner a2]
    _ = idsV1 s * ∑ a2, q' a2 := by rw [← Finset.mul_sum]
    _ = idsV1 s := by rw [hq'.2, mul_one]
end Csg
