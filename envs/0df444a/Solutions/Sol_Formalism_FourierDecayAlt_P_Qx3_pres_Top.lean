-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.pres_Top
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-24T17:29:16.954903+00:00
-- url     : https://prove2.me/submissions/0a75ae30-d73b-49f9-a79d-f4d3e5cde5ac

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_csmul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_pres_EH

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
theorem _root_.solution (u : ℂ) (a b : Fin (mdim k r i)) :
    Pres (E := E) i U₀ (Top (EH k r) u (posL k r i a) (posL k r i b)) := by
  intro Φ h
  refine sf_add ?_ (pres_EH a b Φ h)
  by_cases hab : posL k r i a = posL k r i b
  · simpa [hab] using sf_csmul u h
  · simpa [hab] using (sf_zero (E := E))
end Formalism.FourierDecayAlt.P.Qx3
