-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_integrable
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T02:35:14.972563+00:00
-- url     : https://prove2.me/submissions/7839516d-daa7-457f-8f0f-efde29d17d49

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_isAddHaar_muPi
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_continuous_oscillatory_factor

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
theorem _root_.solution (hβ : β ≠ 0) {ψ : (Fin d → ℂ) → ℝ} (hψ : Continuous ψ) (τ : ℝ) {g : (Fin d → ℂ) → V}
    (hg : Continuous g) (hgc : HasCompactSupport g) :
    Integrable (fun x => osc ψ τ x • g x) (muPi β (Fin d)) := by
  have := isAddHaar_muPi d β hβ
  exact ((continuous_oscillatory_factor hψ τ).smul hg).integrable_of_hasCompactSupport hgc.smul_left
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
