-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.G_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T03:46:16.446292+00:00
-- url     : https://prove2.me/submissions/40ecd670-074c-4d6e-bbc3-6c2b48cdb2f0

import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_StatementT
import Definitions.Def_Formalism_ThetaLogCoordinates_ResidueClassEstimates_VandermondeRankEstimates_LogWeylDimensionEstimate

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
open Formalism.InvariantFactorPaths.BranchingDimensions.TDim
namespace Formalism.InvariantFactorPaths.BranchingDimensions.TDim
theorem _root_.solution {la : ℕ → ℤ} {i j : ℕ} (hij : i < j) : G la i j = hh ((la i - la j : ℤ) : ℝ) (j - i) := by
  unfold G hh
  rw [Nat.cast_sub hij.le]
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
