-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.frame_kernel_to_lin_sub_id
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:45:39.826923+00:00
-- url     : https://prove2.me/submissions/00ba649a-7da4-44c6-bf0e-563e4565450f

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_to_euclidean_lin_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_to_euclidean_lin_one
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
variable {m n o : Type} [Fintype m] [Fintype n] [Fintype o] [DecidableEq m] [DecidableEq n]
  [DecidableEq o]
namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates
theorem _root_.solution (c : ℝ) (A : Matrix m n ℂ) :
    frK c (Matrix.toEuclideanLin A) - LinearMap.id
      = Matrix.toEuclideanLin ((c : ℂ) • (Aᴴ * A) - 1) := by
  unfold frK
  rw [to_euclidean_lin_adjoint_eq, ← to_euclidean_lin_mul, map_sub, map_smul, to_euclidean_lin_one]
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
