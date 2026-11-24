-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.matrix_trace_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:29:33.549301+00:00
-- url     : https://prove2.me/submissions/72fd9bf1-e9a9-41c3-91a4-010d4bfe30f9

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice

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
theorem _root_.solution {m m' : Type} [Fintype m] [Fintype m'] (e : m ≃ m')
    (M : Matrix m m ℂ) : (Matrix.reindex e e M).trace = M.trace := by
  unfold Matrix.trace
  rw [← e.symm.sum_comp]
  rfl
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
