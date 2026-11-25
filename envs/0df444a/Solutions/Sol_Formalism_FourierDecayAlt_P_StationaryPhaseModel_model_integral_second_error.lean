-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.model_integral_second_error
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:18:56.352218+00:00
-- url     : https://prove2.me/submissions/e8242bea-ba70-4ec6-a16b-dc3bb55288f7

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_sqrt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_sqrt_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_est
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_model_amplitude_symbol
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_smul_tsupport
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_smul_compact
import Theorems.Thm_P2M_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_P_sym__920f37ab2922

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
theorem _root_.solution {C : ℝ} (hOB : E_OB d 3 β (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) C)
    (hr : 0 < r) (hΓ : 0 < Γ) (hph : E_Phase d r Γ c₁ φ) (hρ0 : 0 < ρ) (hρr : ρ ≤ r)
    (hρ : (Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6) * ρ ≤ c₁ / 2) (hτ : 0 < τ) (hτ1 : τ ≤ 1)
    (hCχ : 0 ≤ Cχ) (hC : ∀ i : ℕ, i ≤ d + 6 → ∀ x, ‖iteratedFDeriv ℝ i (cutB d ρ) x‖ ≤ Cχ)
    (ha : ‖a₀‖ ≤ S) (hl : ‖ℓ‖ ≤ S) {s : ℝ} (hs : s ∈ Set.Icc (0 : ℝ) 1) :
    ‖∫ x, osc (fun y => quad φ y + s * E_P φ y) τ x • ((E_P φ x * E_P φ x) • modelAmplitude d ρ a₀ ℓ x)
        ∂(muPi β (Fin d))‖ ≤
      C * (2 ^ (d + 1 + 3) * (2 ^ (d + 1 + 3) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) *
        ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6))) *
        (2 ^ (d + 1 + 3) * (Cχ * (ρ + 1) ^ (d + 1 + 3)) * (ρ + 2) * S)) * τ ^ (d + 3) := by
  have hS : 0 ≤ S := (norm_nonneg _).trans ha
  have hw : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) ρ, 0 < wt (Real.sqrt τ) x :=
    fun x _ => E_wt_pos (E_sqrt_pos hτ) x
  have hP := E_P_sym' (N := d + 1 + 3) hr hph hρr hτ hτ1 (by omega)
  have hA := model_amplitude_symbol (N := d + 1 + 3) (a₀ := a₀) (ℓ := ℓ) hρ0 (fun i hi => hC i (by omega)) hρ0 (E_sqrt_pos hτ)
    (E_sqrt_le_one hτ1) ha hl
  have h := Sym.smul hw (Sym.mul hw hP hP) hA
  have e : ((3 : ℤ) + 3 + 0) = 2 * ((3 : ℕ) : ℤ) := by norm_num
  rw [e] at h
  refine E_est (q := 3) (by norm_num) hOB hr hph hρr hρ hτ hτ1 hs _ _ (by positivity) ?_ ?_ h
  · exact (E_cut_smul_compact hρ0 _).smul_left
  · exact (tsupport_smul_subset_right _ _).trans (E_cut_smul_tsupport hρ0 _)
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
