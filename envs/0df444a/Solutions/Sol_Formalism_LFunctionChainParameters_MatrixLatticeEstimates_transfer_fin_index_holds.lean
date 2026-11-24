-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.transfer_fin_index_holds
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T10:45:32.49751+00:00
-- url     : https://prove2.me/submissions/cab39539-65a7-49a1-86df-8613f6f7d850

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_hs_sq_reindex
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_matrix_trace_reindex
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_kernel_matrix_reindex
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_weighted_gram_sub_one_reindex
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_quadratic_matrix_fin_reindex

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
theorem _root_.solution : BridgeFin := by
  intro I α _ _ ι _ _ B ga
  refine ⟨fun i j => ?_, fun i => ?_, ?_, ?_, rfl⟩
  · rw [kernel_matrix_reindex, hs_sq_reindex]
  · rw [weighted_gram_sub_one_reindex, hs_sq_reindex]
  · rw [quadratic_matrix_fin_reindex, matrix_trace_reindex]
  · rw [quadratic_matrix_fin_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    exact matrix_trace_reindex (Fintype.equivFin α) (QmG B ga * QmG B ga)
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
