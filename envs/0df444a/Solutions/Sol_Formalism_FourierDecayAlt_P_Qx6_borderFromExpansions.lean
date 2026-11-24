-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx6.borderFromExpansions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T19:24:31.925579+00:00
-- url     : https://prove2.me/submissions/50a16fe8-e876-49d1-ba89-178a9589c89a

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_GeneratorCommutatorQuantumDet
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_SumDualVectorEqZeta
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_ChainRecursionFromSingleDescent
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_borderE_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_borderS_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx6_borderFull_of

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
namespace Formalism.FourierDecayAlt.P.Qx6
theorem _root_.solution : BorderFromExpansions := by
  intro hFC hLC hFR hLR hSk
  exact ⟨borderE_of hFC hLR hSk, borderS_of hLC hFR hSk, borderFull_of hFC hLC hFR hLR hSk⟩
end Formalism.FourierDecayAlt.P.Qx6
