-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.Qx3.pres_chat2L
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-24T18:05:54.459466+00:00
-- url     : https://prove2.me/submissions/a0cd20b1-9247-4ec5-8669-f05009a50c5f

import Definitions.Def_Formalism_HermitianCurvature_StatementQ
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_RegularisedPairingViaPhase
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_UnitaryWeylNormalHolds
import Definitions.Def_Formalism_FormalDegreeBessel_FormalDegreeRatio_GBasic
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_CartanInvolutionConjTransposeMul
import Definitions.Def_Formalism_RealPlaceAnalysis_RealPlaceTaylor_ComplexifiedDerivativeCommutator
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_WeylCellConjTransposeMulApply
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_smul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_const
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_mul
import Theorems.Thm_Formalism_FourierDecayAlt_P_Qx3_sf_sub
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
theorem _root_.solution (u : ℂ) (a a' β β' : Mx k r → Fin (mdim k r i) → ℂ)
    (ha : ∀ j, SmoothFam k r i U₀ (fun _ g => a g j)) (ha' : ∀ j, SmoothFam k r i U₀ (fun _ g => a' g j))
    (hβ : ∀ j, SmoothFam k r i U₀ (fun _ g => β g j)) (hβ' : ∀ j, SmoothFam k r i U₀ (fun _ g => β' g j)) :
    Pres (E := E) i U₀ (chat2L (EH k r) (posL k r i) u a a' β β') := by
  intro Φ h
  unfold chat2L
  refine sf_sum _ fun i₁ _ => sf_sum _ fun i₂ _ => sf_sum _ fun j₁ _ => sf_sum _ fun j₂ _ => ?_
  by_cases hc : i₁ < i₂ ∧ j₁ < j₂
  · simp only [if_pos hc]
    exact sf_smul (sf_mul (sf_mul (sf_const _) (sf_sub (sf_mul (hβ i₁) (hβ' i₂)) (sf_mul (hβ i₂) (hβ' i₁))))
      (sf_sub (sf_mul (ha j₁) (ha' j₂)) (sf_mul (ha j₂) (ha' j₁)))) (pres_qminor _ _ _ Φ h)
  · simp only [if_neg hc]
    exact sf_zero
end Formalism.FourierDecayAlt.P.Qx3
