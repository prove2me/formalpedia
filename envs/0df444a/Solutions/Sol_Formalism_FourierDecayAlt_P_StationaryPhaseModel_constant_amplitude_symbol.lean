-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.constant_amplitude_symbol
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:58.389667+00:00
-- url     : https://prove2.me/submissions/7144c3f3-8abb-4365-a41a-489ccbb9c155

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_const
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
    (hσ1 : σ ≤ 1) {a₀ : V} {S : ℝ} (ha : ‖a₀‖ ≤ S) :
    Sym (Metric.closedBall (0 : Fin d → ℂ) r') (wt σ) 0 N (2 ^ N * (Cχ * (r' + 1) ^ N) * S) (constantAmplitude d ρ a₀) := by
  have hw : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r', 0 < wt σ x := fun x _ => E_wt_pos hσ x
  have h := Sym.smul hw (E_cut_sym hρ hC hr' hσ hσ1)
    (Sym.const (N := N) (m := 0) (K := S) a₀ ((norm_nonneg _).trans ha) hw (fun x _ => by simpa using ha))
  rwa [add_zero] at h
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
