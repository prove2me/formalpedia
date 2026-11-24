-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.pres_EH
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-8
-- created : 2026-11-24T17:08:01.772175+00:00
-- url     : https://prove2.me/submissions/7fd27eec-d915-4923-a2d7-97fcbbe05a10

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_lieLev_of
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_hpart_lie
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_rdV
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_csmul

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
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
variable {i : Fin (r + 1)} {U₀ : Set (XX k r)}
namespace Formalism.FourierDecayAlt.P.Qx3
theorem _root_.solution (a b : Fin (mdim k r i)) :
    Pres (E := E) i U₀ (EH k r (posL k r i a) (posL k r i b)) := by
  intro Φ h
  exact sf_add (sf_rdV (lieLev_of (hpart_lie i a b).1) h)
    (sf_csmul Complex.I (sf_rdV (lieLev_of (hpart_lie i a b).2) h))
end Formalism.FourierDecayAlt.P.Qx3
