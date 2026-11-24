-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.oMul_eq
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T16:37:54.745587+00:00
-- url     : https://prove2.me/submissions/4dcfaaad-2001-4998-a9bf-2e9f551d01ff

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Matrix Finset Filter Topology
open scoped ContDiff
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx6
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
variable {X : Type*} [AddCommGroup X] [Module ℂ X] (H : HatData X)
variable {H}
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution (M N : OM X) (a b : Fin 2) : oMul M N a b = fun f => M a 0 (N 0 b f) + M a 1 (N 1 b f) := by
  funext f
  simp [oMul, Fin.sum_univ_two]
end Formalism.FourierDecayAlt.P.Qx6
