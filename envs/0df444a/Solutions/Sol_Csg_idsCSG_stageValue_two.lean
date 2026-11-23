-- Prove2me | solution 1 for Csg.idsCSG_stageValue_two
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:58:27.055839+00:00
-- url     : https://prove2.me/submissions/746972fb-0e66-4fd8-af46-3f1a38259ec1

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsP2_mem
import Theorems.Thm_Csg_idsQ2_mem
import Theorems.Thm_Csg_idsCSG_payoff_row_two
import Theorems.Thm_Csg_idsCSG_payoff_col_two
import Theorems.Thm_Csg_MatrixGame_value_unique


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) : idsCSG.stageValue s idsV1 = idsV2 s := by
  have huu : (idsCSG.stageGame s idsV1).payoff idsP2 idsQ2 = idsV2 s :=
    idsCSG_payoff_row_two s idsP2_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ PolicyAction,
      (idsCSG.stageGame s idsV1).payoff idsP2 idsQ2 ≤
        (idsCSG.stageGame s idsV1).payoff p' idsQ2 := fun p' hp' =>
    le_of_eq (huu.trans (idsCSG_payoff_row_two s hp').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ AttackAction,
      (idsCSG.stageGame s idsV1).payoff idsP2 q' ≤
        (idsCSG.stageGame s idsV1).payoff idsP2 idsQ2 := fun q' hq' =>
    le_of_eq ((idsCSG_payoff_col_two s hq').trans huu.symm)
  have hval := (idsCSG.stageGame s idsV1).value_unique idsP2_mem idsQ2_mem hrow hcol
  change (idsCSG.stageGame s idsV1).value = idsV2 s
  rw [← hval]
  exact huu
end Csg
