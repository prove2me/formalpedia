-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.quadratic_matrix_fin_reindex
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:29:34.143509+00:00
-- url     : https://prove2.me/submissions/9a75547e-ccb4-4373-a829-f0463ba4f7cc

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
theorem _root_.solution {I α : Type} [Fintype I] [Fintype α] {ι : I → Type} [∀ i, Fintype (ι i)]
    (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) :
    HilbertSchmidtNormSquare.Qm (toFin B) ga
      = Matrix.reindex (Fintype.equivFin α) (Fintype.equivFin α) (QmG B ga) := by
  unfold HilbertSchmidtNormSquare.Qm QmG toFin
  rw [← Matrix.coe_reindexLinearEquiv ℂ ℂ, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [Matrix.coe_reindexLinearEquiv, Matrix.reindex_apply, Matrix.conjTranspose_submatrix,
    Matrix.submatrix_mul_equiv, Matrix.submatrix_smul, Pi.smul_apply]
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
