-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.quadratic_transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T10:45:12.118838+00:00
-- url     : https://prove2.me/submissions/8788515e-62db-446c-9bd3-35d00c4b8a32

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_to_euclidean_lin_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_to_euclidean_lin_trace
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_weighted_frame_operator_to_lin

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Module NumberField Matrix
open Formalism.CorankShareLayerCake.FR Formalism.HN
noncomputable section
open Formalism Formalism.LFunctionChainParameters Formalism.LFunctionChainParameters.MatrixLatticeEstimates
open Formalism.LFunctionChainParameters.HilbertSchmidtNormSquare (hsSq)
namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates
theorem _root_.solution : BridgeQ := by
  intro I α _ _ _ ι _ _ B ga
  rw [weighted_frame_operator_to_lin, ← to_euclidean_lin_mul, to_euclidean_lin_trace, to_euclidean_lin_trace]
  exact ⟨rfl, rfl⟩
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
