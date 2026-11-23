-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.linear_amplitude_symbol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:58.368842+00:00
-- url     : https://prove2.me/submissions/3506dbb7-3666-4d35-baa5-61513fd566ed

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_sym

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
    (hσ1 : σ ≤ 1) {ℓ : (Fin d → ℂ) →L[ℝ] V} {S : ℝ} (hl : ‖ℓ‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) 1 N (2 ^ N * (Cχ * (r' + 1) ^ N) * S) (linearAmplitude d ρ ℓ) := by
  have hw : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r', 0 < wt σ x := fun x _ => E_wt_pos hσ x
  have h := Sym.smul hw (E_cut_sym hρ hC hr' hσ hσ1)
    ((Sym.clm (A := Metric.closedBall (0 : Fin d → ℂ) r') (N := N) ℓ hσ).mono hw le_rfl hl)
  rwa [zero_add] at h
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
