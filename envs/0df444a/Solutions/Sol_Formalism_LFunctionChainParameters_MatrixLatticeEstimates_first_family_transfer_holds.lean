-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.first_family_transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T11:05:55.905406+00:00
-- url     : https://prove2.me/submissions/51c2c183-9031-4da8-a291-a9eb97755ca5

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_quadratic_transfer_holds
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_transfer_fin_index_holds

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
theorem _root_.solution : FrameTraceRatioFinEquiv := by
  intro I α _ _ ι _ _ B ga η
  classical
  obtain ⟨-, -, h3, h4, -⟩ := transfer_fin_index_holds I α ι B ga
  obtain ⟨q1, q2⟩ := quadratic_transfer_holds I α ι B ga
  unfold HilbertSchmidtNormSquare.F1 FrameTraceRatioLinear
  rw [h3, h4, q1, q2]
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
