-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.sum_drop
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:42:44.438467+00:00
-- url     : https://prove2.me/submissions/e2ddc0b3-08b9-48d6-9811-bffc4d60828f

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
theorem _root_.solution : ∀ (l : List ℕ) (u : ℕ), (l.drop u).sum = ∑ j ∈ Ico u l.length, l.getD j 0
  | [], u => by simp
  | a :: t, 0 => by
      have e := Finset.sum_Ico_add' (fun j => (a :: t).getD j 0) 0 t.length 1
      have h := solution t 0
      simp only [List.drop_zero, List.getD_cons_succ, zero_add] at e h
      rw [List.drop_zero, List.sum_cons, List.length_cons,
        Finset.sum_eq_sum_Ico_succ_bot (by omega), zero_add, ← e, h, List.getD_cons_zero]
  | a :: t, u + 1 => by
      have e := Finset.sum_Ico_add' (fun j => (a :: t).getD j 0) u t.length 1
      simp only [List.getD_cons_succ] at e
      rw [List.drop_succ_cons, List.length_cons, ← e, solution t u]
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
