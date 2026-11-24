-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.hilbert_schmidt_transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:56.579865+00:00
-- url     : https://prove2.me/submissions/ab308547-0010-4c98-9c37-84674d2d7114

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_hs_norm_sq_to_euclidean_lin
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_frame_kernel_to_lin_sub_id
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_weighted_gram_eq_smul

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
theorem _root_.solution : BridgeHS := by
  intro I α _ ι _ _ B ga i hi
  classical
  rw [frame_kernel_to_lin_sub_id, hs_norm_sq_to_euclidean_lin, weighted_gram_eq_smul B ga i hi]
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
