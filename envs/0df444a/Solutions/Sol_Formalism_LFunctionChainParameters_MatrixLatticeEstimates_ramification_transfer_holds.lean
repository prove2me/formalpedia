-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.ramification_transfer_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:29:34.745749+00:00
-- url     : https://prove2.me/submissions/138aac00-4fce-4ae2-b56f-04fa614e0376

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
theorem _root_.solution : BridgeRam := by
  intro I α _ ιf ι _ _ _ Bf Vr
  constructor
  · funext i
    unfold toFin HilbertSchmidtNormSquare.Bram toFinV
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
  · unfold HilbertSchmidtNormSquare.Isom toFinV
    refine forall_congr' fun i => ?_
    simp only [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv]
    constructor
    · intro h
      have := congrArg (fun M => M.submatrix (Fintype.equivFin (ι i)) (Fintype.equivFin (ι i))) h
      simpa using this
    · intro h
      rw [h, Matrix.submatrix_one_equiv]
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
