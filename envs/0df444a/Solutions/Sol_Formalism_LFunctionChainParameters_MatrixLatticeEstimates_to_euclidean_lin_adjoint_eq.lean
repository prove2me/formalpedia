-- Prove2me | solution 1 for Formalism.LFunctionChainParameters.MatrixLatticeEstimates.to_euclidean_lin_adjoint_eq
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-22T22:55:01.693909+00:00
-- url     : https://prove2.me/submissions/b7ba389b-5d97-4262-9784-64e96e63b7d6

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
variable {m n o : Type} [Fintype m] [Fintype n] [Fintype o] [DecidableEq m] [DecidableEq n]
  [DecidableEq o]
namespace Formalism.LFunctionChainParameters.MatrixLatticeEstimates
theorem _root_.solution (A : Matrix m n ℂ) :
    LinearMap.adjoint (Matrix.toEuclideanLin A) = Matrix.toEuclideanLin Aᴴ :=
  (Matrix.toEuclideanLin_conjTranspose_eq_adjoint A).symm
end Formalism.LFunctionChainParameters.MatrixLatticeEstimates
