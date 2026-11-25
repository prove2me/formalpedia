-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.real_core
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-25T01:26:18.246578+00:00
-- url     : https://prove2.me/submissions/fa2a924f-9d5b-4b21-b442-b13eb8cf7a3d

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_taylor
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_quad_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_OB_exists
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_ph_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_est_u
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_modelAmplitude_eq_add
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_smul_compact
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_model_integral_second_error
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_cut_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_linear_amplitude_integral_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_model_integral_first_error
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_a_zero_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_a_fderiv_le
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_u_support
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_E_u_sym

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
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (β : ℂ) (hβ : β ≠ 0) (r Γ c₁ : ℝ) (hr : 0 < r) (hΓ : 0 < Γ) (hc₁ : 0 < c₁) :
    ∃ ρ : ℝ, 0 < ρ ∧ ρ ≤ r ∧ ∃ C : ℝ, ∀ (φ : (Fin d → ℂ) → ℝ) (τ : ℝ), 0 < τ → τ ≤ 1 →
      ContDiff ℝ (d + 6 : ℕ) φ →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∀ i : ℕ, i ≤ d + 6 → ‖iteratedFDeriv ℝ i φ x‖ ≤ Γ) →
      fderiv ℝ φ 0 = 0 →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin d → ℂ) → V) (S : ℝ),
        ContDiff ℝ (2 * d + 2 : ℕ) a → Function.support a ⊆ Metric.closedBall 0 r →
        (∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ‖∫ x, osc φ τ x • a x ∂(muPi β (Fin d)) -
            (∫ x, osc (quad φ) τ x * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))) • a 0‖ ≤ C * S * τ ^ (d + 1) := by
  have hKP0 : 0 < ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) := by positivity
  obtain ⟨ρ, hρdef⟩ : ∃ ρ : ℝ, ρ = (min r (c₁ / (2 * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6))))) := ⟨_, rfl⟩
  have hρ0 : 0 < ρ := by rw [hρdef]; exact lt_min hr (by positivity)
  have hρr : ρ ≤ r := by rw [hρdef]; exact min_le_left _ _
  have hρ : ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) * ρ ≤ c₁ / 2 := by
    calc ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) * ρ ≤ ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) * (c₁ / (2 * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)))) :=
          mul_le_mul_of_nonneg_left (by rw [hρdef]; exact min_le_right _ _) hKP0.le
      _ = c₁ / 2 := by field_simp
  obtain ⟨C1, hC1, hOB1⟩ := E_OB_exists d 1 β hβ (Γ * (r + 1) ^ (d + 5)) c₁ hc₁
  obtain ⟨C2, hC2, hOB2⟩ := E_OB_exists d 2 β hβ (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) (half_pos hc₁)
  obtain ⟨C3, hC3, hOB3⟩ := E_OB_exists d 3 β hβ (Γ + Γ * (r + 1) ^ (d + 5)) (c₁ / 2) (half_pos hc₁)
  obtain ⟨Cχ, hCχ, hC⟩ := E_cut_bound (d := d) hρ0 (d + 6)
  refine ⟨ρ, hρ0, hρr,
    C1 * ((1 + 2 ^ (d + 2) * (Cχ * (r + 1) ^ (d + 2)) * (r + 2)) * (r + 1) ^ (d + 2)) +
      C3 * (2 ^ (d + 1 + 3) * (2 ^ (d + 1 + 3) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6))) *
        (2 ^ (d + 1 + 3) * (Cχ * (ρ + 1) ^ (d + 1 + 3)) * (ρ + 2))) +
      2 * (C2 * (2 ^ (d + 1 + 2) * ((Γ + Γ * (r + 1) ^ 2) * (r + 1) ^ (d + 6)) * (2 ^ (d + 1 + 2) * (Cχ * (ρ + 1) ^ (d + 1 + 2))))), ?_⟩
  intro φ τ hτ hτ1 hsm hbdφ hcrit hlow V _ _ _ a S ha hsupp hbd
  have hph : E_Phase d r Γ c₁ φ := ⟨hsm, hbdφ, hcrit, hlow⟩
  have ha0 := E_a_zero_le hbd
  have hl := E_a_fderiv_le hbd
  have hS : 0 ≤ S := (norm_nonneg _).trans ha0
  have hφc : Continuous φ := hsm.continuous
  have hqc : Continuous (quad φ) := (E_quad_contDiff φ 0).continuous
  have hPc : Continuous (E_P φ) := hφc.sub hqc
  have hχc := E_cut_continuous (d := d) hρ0
  have hac : Continuous a := ha.continuous
  have hcc : Continuous (modelAmplitude d ρ (a 0) (fderiv ℝ a 0)) :=
    hχc.smul (continuous_const.add (fderiv ℝ a 0).continuous)
  have hccs : HasCompactSupport (modelAmplitude d ρ (a 0) (fderiv ℝ a 0)) := E_cut_smul_compact hρ0 _
  have huc : Continuous (E_u d ρ a) := hac.sub hcc
  have husupp := E_u_support hρ0 hρr hsupp
  have hucs : HasCompactSupport (E_u d ρ a) :=
    HasCompactSupport.of_support_subset_isCompact (isCompact_closedBall _ _) husupp
  have huts : tsupport (E_u d ρ a) ⊆ Metric.closedBall 0 r := closure_minimal husupp Metric.isClosed_closedBall

  have hTu := E_est_u hOB1 hr hph hτ hτ1 (E_u d ρ a) _ (by positivity) hucs huts
    (E_u_sym hr hρ0 hτ hτ1 hCχ hC ha hbd)
  have hTay := E_taylor hβ (quad φ) (E_P φ) hqc hPc τ hτ (modelAmplitude d ρ (a 0) (fderiv ℝ a 0)) hcc hccs _
    (fun s hs => model_integral_second_error hOB3 hr hΓ hph hρ0 hρr hρ hτ hτ1 hCχ hC ha0 hl hs)
  rw [E_ph_one] at hTay
  have hT1 := model_integral_first_error hβ hOB2 hr hΓ hph hρ0 hρr hρ hτ hτ1 hCχ hC ha0 hl

  have hsplit : ∫ x, osc φ τ x • a x ∂(muPi β (Fin d)) =
      ∫ x, osc φ τ x • E_u d ρ a x ∂(muPi β (Fin d)) +
        ∫ x, osc φ τ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x ∂(muPi β (Fin d)) := by
    rw [← integral_add (E_integrable hβ hφc τ huc hucs) (E_integrable hβ hφc τ hcc hccs)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [← smul_add, E_u, sub_add_cancel]
  have hmodel : ∫ x, osc (quad φ) τ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x ∂(muPi β (Fin d)) =
      (∫ x, osc (quad φ) τ x * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))) • a 0 := by
    have i0 : Integrable (fun x => osc (quad φ) τ x • constantAmplitude d ρ (a 0) x) (muPi β (Fin d)) :=
      E_integrable hβ hqc τ (hχc.smul continuous_const) (E_cut_smul_compact hρ0 _)
    have i1 : Integrable (fun x => osc (quad φ) τ x • linearAmplitude d ρ (fderiv ℝ a 0) x) (muPi β (Fin d)) :=
      E_integrable hβ hqc τ (hχc.smul (fderiv ℝ a 0).continuous) (E_cut_smul_compact hρ0 _)
    simp_rw [modelAmplitude_eq_add, smul_add]
    rw [integral_add i0 i1, linear_amplitude_integral_zero hβ hρ0, add_zero, ← integral_smul_const]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [constantAmplitude]
    rw [mul_smul, Complex.coe_smul]
  have key : ∫ x, osc φ τ x • a x ∂(muPi β (Fin d)) -
      (∫ x, osc (quad φ) τ x * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))) • a 0 =
      ∫ x, osc φ τ x • E_u d ρ a x ∂(muPi β (Fin d)) +
      (∫ x, osc φ τ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x ∂(muPi β (Fin d)) -
        ∫ x, osc (quad φ) τ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x ∂(muPi β (Fin d)) -
        (Complex.I / (τ : ℂ)) • ∫ x, osc (quad φ) τ x • (E_P φ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x)
          ∂(muPi β (Fin d))) +
      (Complex.I / (τ : ℂ)) • ∫ x, osc (quad φ) τ x • (E_P φ x • modelAmplitude d ρ (a 0) (fderiv ℝ a 0) x)
          ∂(muPi β (Fin d)) := by
    rw [hsplit, ← hmodel]
    abel
  rw [key]
  refine (norm_add₃_le).trans ?_
  have hI : ‖(Complex.I / (τ : ℂ))‖ = 1 / τ := by
    rw [norm_div, Complex.norm_I, Complex.norm_real, Real.norm_of_nonneg hτ.le]
  rw [norm_smul, hI]
  have hT1' := mul_le_mul_of_nonneg_left hT1 (by positivity : 0 ≤ 1 / τ)
  refine (add_le_add (add_le_add hTu hTay) hT1').trans (le_of_eq ?_)
  have e3 : τ ^ (d + 3) = τ ^ (d + 1) * τ ^ 2 := by ring
  have e2 : τ ^ (d + 2) = τ ^ (d + 1) * τ := by ring
  rw [e3, e2]
  field_simp
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
