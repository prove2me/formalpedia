-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.D_compare
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:54:04.131749+00:00
-- url     : https://prove2.me/submissions/af556754-4be5-4427-951a-d8e4f120b54b

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_mono
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_comp_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_clm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_isAddHaar_muPi
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_osc_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_wt_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_sym_cast
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_compact
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_nonneg
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_cut_le_one
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_amp
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_bilC_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_phi_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_phi_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_phi_lower
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_psi_eq_osc
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_continuous
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_gau_integrable
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_osc_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_D_osc_continuous

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open Formalism.FourierDecayAlt.G MeasureTheory Filter Topology Matrix
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.StationaryPhaseModel
noncomputable section
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (hd : 0 < d) (β : ℂ) (hβ : β ≠ 0) (ρ Γ Λ : ℝ) (hρ : 0 < ρ) (hΓ : 0 < Γ) (hΛ : 0 < Λ) :
    ∃ C : ℝ, ∀ H : Matrix (Fin d) (Fin d) ℂ, H.IsSymm → (∀ i j, ‖H i j‖ ≤ Γ) →
      (∀ x : Fin d → ℂ, ‖x‖ ≤ Λ * ‖H *ᵥ x‖) → ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ 1 → ∀ δ : ℝ, 0 < δ → δ ≤ 1 →
        ‖∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d)) -
            gaussInt β d H t δ‖ ≤ C * ‖t‖ ^ (d + 1) := by
  have hβ0 : 0 < ‖β‖ := norm_pos_iff.2 hβ
  obtain ⟨C, hC0, hC⟩ := osc_bound d 1 β hβ (‖β‖ * (d * (d * Γ))) (‖β‖ / (4 * Λ)) (by positivity)
  obtain ⟨K, hK0, hK⟩ := D_amp d (d + 1 + 1) (by omega) hρ
  refine ⟨C * K, ?_⟩
  intro H hs hH hlow t ht ht1 δ hδ hδ1
  have := isAddHaar_muPi d β hβ
  have hτ : 0 < ‖t‖ := norm_pos_iff.2 ht
  set τ := ‖t‖ with hτdef
  set σ := Real.sqrt τ with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hτ
  have hσ1 : σ ≤ 1 := Real.sqrt_le_one.2 ht1
  set c : ℂ := β * (τ : ℂ) / t with hcdef
  have hcn : ‖c‖ = ‖β‖ := by
    rw [hcdef, norm_div, norm_mul, Complex.norm_real, Real.norm_of_nonneg hτ.le, ← hτdef]
    field_simp
  have hc0 : c ≠ 0 := by rw [← norm_pos_iff, hcn]; exact hβ0
  set φ := D_phi d c H with hφdef
  have hφc : ∀ n : ℕ, ContDiff ℝ n φ := D_phi_contDiff d c H Γ hΓ.le hH
  have hφcont : Continuous φ := (hφc 0).continuous
  have hoscc : Continuous (osc φ τ) := D_osc_continuous hφcont τ
  have hpsi : ∀ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) = osc φ τ x := D_psi_eq_osc d β t ht H
  have hφS : Sym (Set.univ : Set (Fin d → ℂ)) (wt σ) 1 (d + 1 + 1) (‖β‖ * (d * (d * Γ))) (fderiv ℝ φ) := by
    rw [hφdef, D_phi_fderiv d c H hs Γ hΓ.le hH]
    refine (Sym.clm (D_bilC d c H Γ hΓ.le hH) hσ).mono (fun x _ => D_wt_pos hσ x) le_rfl ?_
    rw [← hcn]
    exact D_bilC_norm d c H Γ hΓ.le hH
  have hφl : ∀ x ∈ (Set.univ : Set (Fin d → ℂ)), ∃ l : Fin d × Bool,
      ‖β‖ / (4 * Λ) * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)| := by
    intro x _
    rw [← hcn]
    exact D_phi_lower d hd c hc0 H hs Γ hΓ.le hH hΛ hlow x

  set b : (Fin d → ℂ) → ℝ := fun x => cutB d ρ x - D_gau d δ x with hbdef
  have hbcont : Continuous b := ((D_cut_contDiff d hρ 0).continuous).sub (D_gau_continuous d δ)
  have hχint : Integrable (cutB d ρ) (muPi β (Fin d)) :=
    ((D_cut_contDiff d hρ 0).continuous).integrable_of_hasCompactSupport (D_cut_compact d hρ)
  have hGint := D_gau_integrable d β hβ δ hδ
  have hbint : Integrable b (muPi β (Fin d)) := hχint.sub hGint
  have hR : ∀ R : ℝ, 1 ≤ R →
      ‖∫ x, osc φ τ x • (((cutB d 2 (R⁻¹ • x) * b x : ℝ)) : ℂ) ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + 1) := by
    intro R hR1
    have hR0 : 0 < R := by linarith
    refine hC Set.univ φ τ hτ (hφc _) hφS hφl ℂ _ K hK0 ?_ (Set.subset_univ _) ?_
    · have h1 : HasCompactSupport (fun x : Fin d → ℂ => cutB d 2 (R⁻¹ • x)) :=
        (D_cut_compact d two_pos).comp_smul (inv_pos.2 hR0).ne'
      have h2 : HasCompactSupport (fun x : Fin d → ℂ => cutB d 2 (R⁻¹ • x) * b x) := h1.mul_right
      exact h2.comp_left (g := fun r : ℝ => (r : ℂ)) (by simp)
    · have h1 := (hK δ hδ hδ1 σ hσ hσ1 R hR1).comp_clm Complex.ofRealCLM
      rw [Complex.ofRealCLM_norm, one_mul] at h1
      exact D_sym_cast (by norm_num) h1

  have hlim : Tendsto (fun n : ℕ => ∫ x, osc φ τ x • (((cutB d 2 (((n : ℝ) + 1)⁻¹ • x) * b x : ℝ)) : ℂ)
      ∂(muPi β (Fin d))) atTop (𝓝 (∫ x, osc φ τ x • ((b x : ℝ) : ℂ) ∂(muPi β (Fin d)))) := by
    refine tendsto_integral_of_dominated_convergence (fun x => ‖b x‖) (fun n => ?_) hbint.norm (fun n => ?_) ?_
    · refine Continuous.aestronglyMeasurable ?_
      have h2 : Continuous (fun x : Fin d → ℂ => cutB d 2 (((n : ℝ) + 1)⁻¹ • x)) :=
        ((D_cut_contDiff d two_pos 0).continuous).comp (continuous_const_smul _)
      exact hoscc.smul (Complex.continuous_ofReal.comp (h2.mul hbcont))
    · refine Filter.Eventually.of_forall fun x => ?_
      rw [norm_smul, D_osc_norm, one_mul, Complex.norm_real, norm_mul]
      have h3 : ‖cutB d 2 (((n : ℝ) + 1)⁻¹ • x)‖ ≤ 1 := by
        rw [Real.norm_of_nonneg (D_cut_nonneg d two_pos _)]
        exact D_cut_le_one d two_pos _
      calc _ ≤ 1 * ‖b x‖ := by gcongr
        _ = ‖b x‖ := one_mul _
    · refine Filter.Eventually.of_forall fun x => ?_
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [eventually_ge_atTop ⌈‖x‖⌉₊] with n hn
      have h4 : ‖x‖ ≤ (n : ℝ) + 1 := by
        have := (Nat.le_ceil ‖x‖).trans (by exact_mod_cast hn : ((⌈‖x‖⌉₊ : ℕ) : ℝ) ≤ (n : ℝ))
        linarith
      have h5 : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have h6 : ‖((n : ℝ) + 1)⁻¹ • x‖ ≤ 2 / 2 := by
        rw [norm_smul, Real.norm_of_nonneg (inv_pos.2 h5).le, inv_mul_le_iff₀ h5]
        linarith
      rw [D_cut_one d two_pos h6, one_mul]
  have hmain : ‖∫ x, osc φ τ x • ((b x : ℝ) : ℂ) ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + 1) :=
    le_of_tendsto' hlim.norm (fun n => hR _ (by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]))

  have hI1 : Integrable (fun x : Fin d → ℂ => osc φ τ x * ((cutB d ρ x : ℝ) : ℂ)) (muPi β (Fin d)) := by
    refine hχint.norm.mono' (hoscc.mul (Complex.continuous_ofReal.comp
      (D_cut_contDiff d hρ 0).continuous)).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, D_osc_norm, one_mul, Complex.norm_real]
  have hI2 : Integrable (fun x : Fin d → ℂ => ((D_gau d δ x : ℝ) : ℂ) * osc φ τ x) (muPi β (Fin d)) := by
    refine hGint.norm.mono' ((Complex.continuous_ofReal.comp (D_gau_continuous d δ)).mul
      hoscc).aestronglyMeasurable (Filter.Eventually.of_forall fun x => ?_)
    rw [norm_mul, D_osc_norm, mul_one, Complex.norm_real]
  have hid : ∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d)) -
      gaussInt β d H t δ = ∫ x, osc φ τ x • ((b x : ℝ) : ℂ) ∂(muPi β (Fin d)) := by
    unfold gaussInt
    simp_rw [hpsi]
    refine (integral_sub hI1 hI2).symm.trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hbdef, smul_eq_mul, Complex.ofReal_sub, D_gau]
    ring
  rw [hid]
  exact hmain
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
