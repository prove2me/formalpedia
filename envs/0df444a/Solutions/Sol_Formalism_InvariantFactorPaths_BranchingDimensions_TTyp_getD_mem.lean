-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.getD_mem
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:36:31.803683+00:00
-- url     : https://prove2.me/submissions/ad54cb2e-c878-4e4e-b212-085728a78772

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
theorem _root_.solution {l : List ℕ} {t : ℕ} (h : t < l.length) : l.getD t 0 ∈ l := by
  induction l generalizing t with
  | nil => simp at h
  | cons x l ih =>
    cases t with
    | zero => simp
    | succ t =>
      rw [List.getD_cons_succ]
      exact List.mem_cons_of_mem _ (ih (by simpa using h))
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
