-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension.extW_mk
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:48:40.683219+00:00
-- url     : https://prove2.me/submissions/97a8ae3b-cace-41fc-a2a3-21d2b9d00321

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_TTotal

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
open Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
namespace Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
theorem _root_.solution {n : ℕ} (f : ℕ → ℤ) (m : ℕ) :
    extW (fun l : Fin n => f l.val) m = if m < n then f m else 0 := by
  unfold extW
  by_cases h : m < n <;> simp [h]
end Formalism.InvariantFactorPaths.BranchingDimensions.extendedWeightWeylDimension
