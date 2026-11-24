-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.chainFromStep
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-2
-- created : 2026-11-24T20:37:26.741616+00:00
-- url     : https://prove2.me/submissions/d04a7ad1-3ab7-405a-9fd2-901e97ba1d56

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_chainAll_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_cVv_of

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
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution : ChainFromStep := by
  intro hCS hR hRG hFO hTP hLL hW
  exact ⟨chainAll_of hCS hR hRG hFO hTP hLL hW, cVv_of (chainAll_of hCS hR hRG hFO hTP hLL hW) hR hRG hFO hTP hLL⟩
end Formalism.FourierDecayAlt.P.Qx6
