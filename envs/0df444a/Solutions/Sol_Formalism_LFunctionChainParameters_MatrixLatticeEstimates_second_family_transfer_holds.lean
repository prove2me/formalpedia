-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.second_family_transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T11:29:04.055752+00:00
-- url     : https://prove2.me/submissions/38a35c60-a3e3-464f-87a6-1b56244db08c

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_hilbert_schmidt_transfer_holds
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
theorem _root_.solution : FrameDeviationFinEquiv := by
  intro I α _ _ ι _ _ B ga e hga
  obtain ⟨-, h2, -, -, h5⟩ := transfer_fin_index_holds I α ι B ga
  unfold HilbertSchmidtNormSquare.F2 FrameDeviationLinear
  rw [h5]
  simp only [h2, fun i => hilbert_schmidt_transfer_holds I α ι B ga i (hga i)]
  rfl
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
