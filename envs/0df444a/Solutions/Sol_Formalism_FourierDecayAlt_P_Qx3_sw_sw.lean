-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.sw_sw
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T16:25:01.321662+00:00
-- url     : https://prove2.me/submissions/e0437730-a626-48a7-b0f7-425e70dec576

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sw_e
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sw_es
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sw_o
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_tri

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
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.Qx3
open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt.Q
attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace
variable {k r : ℕ}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution (l : Fin r) (q : Fin (2 * r + k + 1)) : sw k l (sw k l q) = q := by
  rcases tri l q with h | h | ⟨h1, h2⟩
  · rw [h, sw_e, sw_es]
  · rw [h, sw_es, sw_e]
  · rw [sw_o l h1 h2, sw_o l h1 h2]
end Formalism.FourierDecayAlt.P.Qx3
