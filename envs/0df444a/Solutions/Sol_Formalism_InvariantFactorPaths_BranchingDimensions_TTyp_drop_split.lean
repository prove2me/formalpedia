-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TTyp.drop_split
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:46:12.219547+00:00
-- url     : https://prove2.me/submissions/a5ab7945-09be-4e01-80ae-aeefeeb4c0e8

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_AtypicalWeightBoundOf
-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
section
noncomputable section
open scoped BigOperators
open Finset
namespace Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
namespace TTyp
end TTyp
namespace TTyp
end TTyp
namespace TTyp
private theorem list_sum_drop_eq_getD_add_sum_drop_succ (l : List ℕ) (u : ℕ) : (l.drop u).sum = l.getD u 0 + (l.drop (u + 1)).sum := by
  induction l generalizing u with
  | nil => simp
  | cons x l ih =>
    cases u with
    | zero => simp
    | succ u => simpa using ih u
end TTyp
namespace TTyp
end TTyp
end Formalism.InvariantFactorPaths.BranchingDimensions
end
end

set_option autoImplicit false
noncomputable section
open scoped BigOperators
open Finset
open Formalism Formalism.InvariantFactorPaths Formalism.InvariantFactorPaths.BranchingDimensions
open Letters
open Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
theorem _root_.solution (l : List ℕ) (u : ℕ) : (l.drop u).sum = l.getD u 0 + (l.drop (u + 1)).sum := list_sum_drop_eq_getD_add_sum_drop_succ l u
end Formalism.InvariantFactorPaths.BranchingDimensions.TTyp
