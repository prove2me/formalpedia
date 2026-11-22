-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.tailPos_mono
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T21:30:14.100798+00:00
-- url     : https://prove2.me/submissions/81ab9a50-e679-41b2-883d-c819e60b61b0

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
theorem _root_.solution {n : ℕ} {a b : ℕ → ℤ} (h : ∀ m, m < n → a m ≤ b m) (u : ℕ) :
    tailPos n a u ≤ tailPos n b u := by
  unfold tailPos
  apply Finset.sum_le_sum
  intro m hm
  simp only [Finset.mem_filter, Finset.mem_range] at hm
  exact max_le_max (h m hm.1) le_rfl
end Formalism.InvariantFactorPaths.BranchingDimensions
