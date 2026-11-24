-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.hs_norm_sq_to_euclidean_lin
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T10:29:32.356311+00:00
-- url     : https://prove2.me/submissions/dff0b51c-c024-4715-b668-dfc73b71e3e0

import Definitions.Def_Formalism_SizeWindowBrackets_FrameTraceRatioFinEquiv
import Definitions.Def_Formalism_HarderNarasimhan_ShiftInvariance
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_TraceConjTransposeMulSelf
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_CorollaryModelSideCondition
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_ExistsNsmulMem
import Definitions.Def_Formalism_SizeWindowBrackets_ChainSlopeWindows_JointDModelAppliesUnitLattice
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_to_euclidean_lin_mul
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_to_euclidean_lin_trace
import Theorems.Thm_Formalism_LFunctionChainParameters_MatrixLatticeEstimates_to_euclidean_lin_adjoint_eq
import Theorems.Thm_Formalism_LFunctionChainParameters_HilbertSchmidtNormSquare_hsSq_eq_re


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
theorem _root_.solution (A : Matrix m n ℂ) : hs2 (Matrix.toEuclideanLin A) = hsSq A := by
  unfold hs2
  rw [to_euclidean_lin_adjoint_eq, ← to_euclidean_lin_mul, to_euclidean_lin_trace, HilbertSchmidtNormSquare.hsSq_eq_re]
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
