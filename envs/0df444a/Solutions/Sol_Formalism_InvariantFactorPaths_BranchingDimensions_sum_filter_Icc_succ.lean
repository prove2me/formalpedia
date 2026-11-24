-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.sum_filter_Icc_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-24T08:44:42.027934+00:00
-- url     : https://prove2.me/submissions/c2fe3c4c-5cf2-4df2-8aa5-517af9590369

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_N0LeNs

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
namespace Formalism.InvariantFactorPaths.BranchingDimensions
theorem _root_.solution (p : ℕ → Prop) [DecidablePred p] (f : ℕ → ℕ) (a i : ℕ) (h : a ≤ i + 1) :
    ∑ l ∈ (Icc a (i + 1)).filter p, f l =
      (∑ l ∈ (Icc a i).filter p, f l) + if p (i + 1) then f (i + 1) else 0 := by
  rw [Finset.sum_filter, Finset.sum_filter, Finset.sum_Icc_succ_top h]
end Formalism.InvariantFactorPaths.BranchingDimensions
