-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.pres_tL
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-7
-- created : 2026-11-24T18:26:09.652738+00:00
-- url     : https://prove2.me/submissions/f7b36a47-8696-48e4-8587-db76e2ddc1c3

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_pres_qminor
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_yv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_ybv
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_pres_chatL
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_pres_chat2L

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
theorem _root_.solution (z z' : Fin (2 * r + k + 1) → ℂ) (Y : ℂ) (p q : Fin 2) :
    Pres (E := E) i U₀ (tL k r z z' i Y p q) := by
  intro Φ h
  fin_cases p <;> fin_cases q
  · show SmoothFam k r i U₀ (fun c => capL k r i (uC k r i Y) (Φ c))
    exact pres_qminor id id _ Φ h
  · show SmoothFam k r i U₀ (fun c g => -(chatL (EH k r) (posL k r i) (uC k r i Y - 1) (fun _ => xv k r z' i)
      (ybv k r z i) (Φ c) g))
    exact sf_neg (pres_chatL (uC k r i Y - 1) (fun _ => xv k r z' i) (ybv k r z i)
      (fun j => sf_const _) (fun j => sf_ybv z j) Φ h)
  · show SmoothFam k r i U₀ (fun c g => -(chatL (EH k r) (posL k r i) (uC k r i Y) (yv k r z i)
      (fun _ => xbv k r z' i) (Φ c) g))
    exact sf_neg (pres_chatL (uC k r i Y) (yv k r z i) (fun _ => xbv k r z' i)
      (fun j => sf_yv z j) (fun j => sf_const _) Φ h)
  · show SmoothFam k r i U₀ (fun c g => -(chat2L (EH k r) (posL k r i) (uC k r i Y - 1) (yv k r z i)
      (fun _ => xv k r z' i) (ybv k r z i) (fun _ => xbv k r z' i) (Φ c) g))
    exact sf_neg (pres_chat2L (uC k r i Y - 1) (yv k r z i) (fun _ => xv k r z' i) (ybv k r z i)
      (fun _ => xbv k r z' i) (fun j => sf_yv z j) (fun j => sf_const _) (fun j => sf_ybv z j)
      (fun j => sf_const _) Φ h)
end Formalism.FourierDecayAlt.P.Qx3
