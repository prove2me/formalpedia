-- Prove2me | solution 1 for Csg.idsCSG_payoff_col_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:56:46.396164+00:00
-- url     : https://prove2.me/submissions/61d79161-db68-4d2f-af4e-d3bf135ca934

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_policyAction_sum
import Theorems.Thm_P2M_Csg_idsCSG_stageGame_A__7bb1bc444f1d
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) {q' : AttackAction → ℝ}
    (hq' : q' ∈ stdSimplex ℝ AttackAction) :
    (idsCSG.stageGame s idsV1).payoff idsP2 q' = idsV2 s := by
  have hinner : ∀ a2, ∑ a1, idsP2 a1 * (idsCSG.stageGame s idsV1).A a1 a2 = idsV2 s := by
    intro a2
    rw [policyAction_sum]
    cases s <;> cases a2 <;>
      simp [idsCSG_stageGame_A', idsR, idsNext, idsP2, idsV1, idsV2] <;> norm_num
  rw [MatrixGame.payoff_eq_sum_mul']
  calc ∑ a2, (∑ a1, idsP2 a1 * (idsCSG.stageGame s idsV1).A a1 a2) * q' a2
      = ∑ a2, idsV2 s * q' a2 := Finset.sum_congr rfl fun a2 _ => by rw [hinner a2]
    _ = idsV2 s * ∑ a2, q' a2 := by rw [← Finset.mul_sum]
    _ = idsV2 s := by rw [hq'.2, mul_one]
end Csg
