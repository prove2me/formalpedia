-- Prove2me | solution 1 for Formalism.InvariantFactorPaths.BranchingDimensions.TDim.hh_le
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:34:29.576648+00:00
-- url     : https://prove2.me/submissions/8ff38eaf-d1a5-400a-a66c-fd4849d8f46c

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
theorem _root_.solution {z : ℝ} {d : ℕ} (hz : 0 ≤ z) (hd : 1 ≤ d) : hh z d ≤ Real.log (1 + z) := by
  have hd' : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hd0 : (0 : ℝ) < d := by linarith
  unfold hh
  apply Real.log_le_log (div_pos (by linarith) hd0)
  rw [div_le_iff₀ hd0]
  nlinarith [mul_nonneg hz (sub_nonneg.mpr hd')]
end Formalism.InvariantFactorPaths.BranchingDimensions.TDim
