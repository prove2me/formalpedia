-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.pres_chatL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:05:55.099583+00:00
-- url     : https://prove2.me/submissions/66209671-d8e0-4152-8942-96b3ad98a160

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_pres_qminor

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
theorem _root_.solution (u : ℂ) (a β : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothFam k r i U₀ (fun _ g => a g j)) (hβ : ∀ j, SmoothFam k r i U₀ (fun _ g => β g j)) :
    Pres (E := E) i U₀ (chatL (EH k r) (posL k r i) u a β) := by
  intro Φ h
  unfold chatL
  exact sf_sum _ fun i' _ => sf_sum _ fun j' _ =>
    sf_smul (sf_mul (sf_mul (sf_const _) (hβ i')) (ha j')) (pres_qminor _ _ _ Φ h)
end Formalism.FourierDecayAlt.P.Qx3
