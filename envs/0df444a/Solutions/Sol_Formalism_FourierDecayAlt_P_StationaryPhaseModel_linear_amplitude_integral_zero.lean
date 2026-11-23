-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.linear_amplitude_integral_zero
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:43:18.076159+00:00
-- url     : https://prove2.me/submissions/3c5a4976-ebd3-411d-8aab-6489322636c7

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_integral_odd
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_osc_quad_neg

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ Cχ S : ℝ} {φ : (Fin d → ℂ) → ℝ}
variable {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
variable {a₀ : V} {ℓ : (Fin d → ℂ) →L[ℝ] V}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hβ : β ≠ 0) (hρ0 : 0 < ρ) :
    ∫ x, osc (quad φ) τ x • linearAmplitude d ρ ℓ x ∂(muPi β (Fin d)) = 0 := by
  refine E_integral_odd hβ _ fun x => ?_
  rw [E_osc_quad_neg]
  simp [linearAmplitude, E_cut_neg hρ0]
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
