-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.Dom.anti
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T00:32:28.053396+00:00
-- url     : https://prove2.me/submissions/044bedf8-7d20-4587-ab6d-62b1810e3719

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
namespace Dom
theorem _root_.solution {n : ℕ} {la : ℕ → ℤ} (h : Dom n la) : ∀ a b, a ≤ b → b < n → la b ≤ la a := by
  intro a b hab hb
  induction b, hab using Nat.le_induction with
  | base => exact le_rfl
  | succ b hab ih => exact (h b hb).trans (ih (by omega))
end Dom
end Formalism.InvariantFactorPaths.BranchingDimensions
