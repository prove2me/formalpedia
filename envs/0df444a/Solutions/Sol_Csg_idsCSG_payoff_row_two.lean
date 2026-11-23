-- Prove2me | solution 1 for Csg.idsCSG_payoff_row_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:56:43.362535+00:00
-- url     : https://prove2.me/submissions/9e402f8b-5dfa-4dd3-8e5b-da41d27221e4

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_attackAction_sum
import Theorems.Thm_P2M_Csg_idsCSG_stageGame_A__7bb1bc444f1d
import Theorems.Thm_Csg_CSG_bwInd_zero
attribute [local simp] Csg.CSG.bwInd_zero



set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) {p' : PolicyAction → ℝ}
    (hp' : p' ∈ stdSimplex ℝ PolicyAction) :
    (idsCSG.stageGame s idsV1).payoff p' idsQ2 = idsV2 s := by
  have hinner : ∀ a1, ∑ a2, (idsCSG.stageGame s idsV1).A a1 a2 * idsQ2 a2 = idsV2 s := by
    intro a1
    rw [attackAction_sum]
    cases s <;> cases a1 <;>
      simp [idsCSG_stageGame_A', idsR, idsNext, idsQ2, idsV1, idsV2] <;> norm_num
  rw [MatrixGame.payoff_eq_sum_mul]
  calc ∑ a1, p' a1 * ∑ a2, (idsCSG.stageGame s idsV1).A a1 a2 * idsQ2 a2
      = ∑ a1, p' a1 * idsV2 s := Finset.sum_congr rfl fun a1 _ => by rw [hinner a1]
    _ = (∑ a1, p' a1) * idsV2 s := by rw [← Finset.sum_mul]
    _ = idsV2 s := by rw [hp'.2, one_mul]
end Csg
