-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_est
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-5
-- created : 2026-11-25T01:05:20.139785+00:00
-- url     : https://prove2.me/submissions/8c9b7cef-bca7-4e2f-a5d6-0b8e0e128ff1

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_subset
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_sym
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_low
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
theorem _root_.solution {q : ℕ} {C : ℝ} (hq : q ≤ 4) (hOB : E_OB d q β (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) C)
    (hr : 0 < r) (hph : E_Phase d r Γ c₁ φ) (hρr : ρ ≤ r)
    (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6) * ρ ≤ c₁ / 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1)
    {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (K : ℝ)
    (hK : 0 ≤ K) (hbc : HasCompactSupport b) (hbs : tsupport b ⊆ Metric.closedBall (0 : Fin d → ℂ) ρ)
    (hb : Sym (Metric.closedBall (0 : Fin d → ℂ) ρ) (wt (Real.sqrt τ)) (2 * (q : ℤ)) (d + 1 + q) K b) :
    ‖∫ x, osc (fun y => quad φ y + s * E_P φ y) τ x • b x ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + q) := by
  refine hOB (Metric.closedBall (0 : Fin d → ℂ) ρ) _ τ hτ ?_ ?_ ?_ V b K hK hbc hbs hb
  · exact E_ph_contDiff (hph.smooth.of_le (by exact_mod_cast (by omega : d + 2 + q ≤ d + 6))) s
  · have h := E_ph_sym (N := d + 5) (by omega) hph.smooth hr (E_sqrt_pos hτ) (E_sqrt_le_one hτ1) hph.crit
      hph.bd hs
    exact (h.subset (Metric.closedBall_subset_closedBall hρr)).mono (fun x _ => E_wt_pos (E_sqrt_pos hτ) x)
      (by omega) le_rfl
  · exact E_ph_low (by omega) hph.smooth hr hph.crit hph.bd hph.low hρr hρ hs
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
