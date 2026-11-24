-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.weighted_gram_sub_one_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:29:27.79442+00:00
-- url     : https://prove2.me/submissions/073f7366-c7ec-4041-a642-cdc4e8aa1e39

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_kernel_matrix_reindex

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
theorem _root_.solution {I α : Type} [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) (i : I) :
    HilbertSchmidtNormSquare.Kd (toFin B) ga i - 1
      = Matrix.reindex (Fintype.equivFin (ι i)) (Fintype.equivFin (ι i)) (KdG B ga i - 1) := by
  unfold HilbertSchmidtNormSquare.Kd KdG
  rw [kernel_matrix_reindex]
  simp only [Matrix.reindex_apply, Matrix.submatrix_sub, Matrix.submatrix_one_equiv, Pi.sub_apply]
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
