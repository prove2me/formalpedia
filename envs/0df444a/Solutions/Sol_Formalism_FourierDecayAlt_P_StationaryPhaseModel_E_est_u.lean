-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_est_u
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:45:58.490798+00:00
-- url     : https://prove2.me/submissions/886f3c06-ea58-420d-a9e6-d96b74bc33b4

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_dphi_sym
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_sqrt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_sqrt_le_one

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
variable {d : ℕ} {β : ℂ} {r Γ c₁ ρ τ : ℝ} {φ : (Fin d → ℂ) → ℝ}
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {C : ℝ} (hOB : E_OB d 1 β (Γ * (r + 1) ^ (d + 5)) c₁ C)
    (hr : 0 < r) (hph : E_Phase d r Γ c₁ φ) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (K : ℝ)
    (hK : 0 ≤ K) (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ Metric.closedBall (0 : Fin d → ℂ) r)
    (hb : Sym (Metric.closedBall (0 : Fin d → ℂ) r) (wt (Real.sqrt τ)) 2 (d + 2) K b) :
    ‖∫ x, osc φ τ x • b x ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + 1) := by
  refine hOB (Metric.closedBall (0 : Fin d → ℂ) r) _ τ hτ ?_ ?_ hph.low V b K hK hbc hbs ?_
  · exact hph.smooth.of_le (by exact_mod_cast (by omega : d + 2 + 1 ≤ d + 6))
  · have h := E_dphi_sym (N := d + 5) (by omega) hph.smooth hr (E_sqrt_pos hτ) (E_sqrt_le_one hτ1) hph.crit
      hph.bd
    exact h.mono (fun x _ => E_wt_pos (E_sqrt_pos hτ) x) (by omega) le_rfl
  · exact_mod_cast hb
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
