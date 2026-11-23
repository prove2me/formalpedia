-- Prove2me | solution 1 for Csg.idsCSG_stageValue
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-23T00:54:04.638164+00:00
-- url     : https://prove2.me/submissions/0069ddf2-bec9-4570-9248-c7bdce7aff3c

import Definitions.Def_Csg_BackwardInduction
import Definitions.Def_Csg_CsgMonotone
import Mathlib.Probability.ProbabilityMassFunction.Monad
import Definitions.Def_Csg_IntrusionDetection
import Theorems.Thm_Csg_idsP_mem
import Theorems.Thm_Csg_idsQ_mem
import Theorems.Thm_Csg_idsCSG_payoff_row
import Theorems.Thm_Csg_idsCSG_payoff_col
import Theorems.Thm_Csg_MatrixGame_value_unique


set_option autoImplicit true
open Csg
namespace Csg
theorem _root_.solution (s : IDSState) : idsCSG.stageValue s (fun _ => 0) = idsV1 s := by
  have huu : (idsCSG.stageGame s (fun _ => 0)).payoff idsP idsQ = idsV1 s :=
    idsCSG_payoff_row s idsP_mem
  have hrow : ∀ p' ∈ stdSimplex ℝ PolicyAction,
      (idsCSG.stageGame s (fun _ => 0)).payoff idsP idsQ ≤
        (idsCSG.stageGame s (fun _ => 0)).payoff p' idsQ := fun p' hp' =>
    le_of_eq (huu.trans (idsCSG_payoff_row s hp').symm)
  have hcol : ∀ q' ∈ stdSimplex ℝ AttackAction,
      (idsCSG.stageGame s (fun _ => 0)).payoff idsP q' ≤
        (idsCSG.stageGame s (fun _ => 0)).payoff idsP idsQ := fun q' hq' =>
    le_of_eq ((idsCSG_payoff_col s hq').trans huu.symm)
  have hval := (idsCSG.stageGame s (fun _ => 0)).value_unique idsP_mem idsQ_mem hrow hcol
  change (idsCSG.stageGame s (fun _ => 0)).value = idsV1 s
  rw [← hval]
  exact huu
end Csg
