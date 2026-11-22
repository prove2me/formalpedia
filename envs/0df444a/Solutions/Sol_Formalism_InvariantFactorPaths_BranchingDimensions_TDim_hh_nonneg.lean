-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:34:29.739827+00:00
-- url     : https://prove2.me/submissions/de301dad-a000-4695-8368-60869efe100f

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
theorem _root_.solution {z : ℝ} {d : ℕ} (hz : 0 ≤ z) (hd : 1 ≤ d) : 0 ≤ hh z d := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  unfold hh
  apply Real.log_nonneg
  rw [one_le_div hd0]
  linarith
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
