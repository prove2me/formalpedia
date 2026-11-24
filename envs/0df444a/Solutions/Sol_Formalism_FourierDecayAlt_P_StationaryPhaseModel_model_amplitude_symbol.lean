-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.model_amplitude_symbol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:29.597112+00:00
-- url     : https://prove2.me/submissions/9d5af543-f0e1-412e-8055-7d430be70b9a

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_lower
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_modelAmplitude_eq_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_constant_amplitude_symbol
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_linear_amplitude_symbol
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_wt_le

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
variable {d : ℕ} {β : ℂ} {ρ : ℝ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (hρ : 0 < ρ) {N : ℕ} {Cχ : ℝ}
    (hC : ∀ i : ℕ, i ≤ N → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ) {r' σ : ℝ} (hr' : 0 < r') (hσ : 0 < σ)
    (hσ1 : σ ≤ 1) {a₀ : V} {ℓ : (Fin d → ℂ) →L[ℝ] V} {S : ℝ} (ha : ‖a₀‖ ≤ S) (hl : ‖ℓ‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) 0 N
      (2 ^ N * (Cχ * (r' + 1) ^ N) * (r' + 2) * S) (modelAmplitude d ρ a₀ ℓ) := by
  have hw : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r', 0 < wt σ x := fun x _ => E_wt_pos hσ x
  have h1 : Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) (0 + ((1 : ℕ) : ℤ)) N
      (2 ^ N * (Cχ * (r' + 1) ^ N) * S) (linearAmplitude d ρ ℓ) := by
    have := linear_amplitude_symbol hρ hC hr' hσ hσ1 hl
    simpa using this
  have h2 := Sym.lower 1 hw (E_wt_le hσ1) h1
  rw [modelAmplitude_eq_add]
  exact ((constant_amplitude_symbol hρ hC hr' hσ hσ1 ha).add h2).mono hw le_rfl (le_of_eq (by ring))
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
