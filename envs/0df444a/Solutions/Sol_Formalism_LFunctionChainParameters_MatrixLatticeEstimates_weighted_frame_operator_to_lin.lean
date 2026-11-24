-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.weighted_frame_operator_to_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T10:29:26.523508+00:00
-- url     : https://prove2.me/submissions/fd32ece7-39a2-494f-a238-6b406b0bc990

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_to_euclidean_lin_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_to_euclidean_lin_adjoint_eq

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
theorem _root_.solution {I α : Type} [Fintype I] [Fintype α] [DecidableEq α] {ι : I → Type}
    [∀ i, Fintype (ι i)] [∀ i, DecidableEq (ι i)] (B : ∀ i, Matrix α (ι i) ℂ) (ga : I → ℝ) :
    frQ ga (fun i => Matrix.toEuclideanLin (B i)) = Matrix.toEuclideanLin (QmG B ga) := by
  unfold frQ QmG
  rw [map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, to_euclidean_lin_mul, to_euclidean_lin_adjoint_eq]
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
