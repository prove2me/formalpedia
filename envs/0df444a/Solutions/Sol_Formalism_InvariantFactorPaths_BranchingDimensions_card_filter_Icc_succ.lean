-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.card_filter_Icc_succ
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:40.200301+00:00
-- url     : https://prove2.me/submissions/959d1303-c03b-4412-a4d2-83fbc85ecb19

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
theorem _root_.solution (p : ℕ → Prop) [DecidablePred p] (a i : ℕ) (h : a ≤ i + 1) :
    ((Icc a (i + 1)).filter p).card = ((Icc a i).filter p).card + if p (i + 1) then 1 else 0 := by
  rw [Finset.card_filter, Finset.card_filter, Finset.sum_Icc_succ_top h]
end Formalism.InvariantFactorPaths.BranchingDimensions
