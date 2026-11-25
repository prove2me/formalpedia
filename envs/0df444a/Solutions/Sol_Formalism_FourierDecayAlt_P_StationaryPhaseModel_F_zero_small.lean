-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.F_zero_small
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-6
-- created : 2026-11-25T01:37:45.766357+00:00
-- url     : https://prove2.me/submissions/d381fc42-c031-4250-95ea-6a176fd2f81f

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_model
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_real_core
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_clm_sum
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_dg_eq
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_H_symm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_H_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_H_lower
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_contDiff
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_bound
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_phi_fderiv
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_norm_psi
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_c_norm
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_osc_phi
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_osc_quad
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_F_lower

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
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution (d : ℕ) (hd : 0 < d) (β : ℂ) (hβ : β ≠ 0) (r Λ : ℝ) (hr : 0 < r) (hΛ : 0 < Λ) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (g : (Fin d → ℂ) → ℂ) (dg : (Fin d → ℂ) → Fin d → ℂ) (H : Matrix (Fin d) (Fin d) ℂ),
      DifferentiableOn ℂ g (Metric.ball 0 (2 * r)) → (∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ‖g x‖ ≤ Λ) →
      (∀ x ∈ Metric.ball (0 : Fin d → ℂ) (2 * r), ∀ k,
        HasDerivAt (fun ξ => g (Function.update x k ξ)) (dg x k) (x k)) →
      (∀ k, dg 0 k = 0) →
      (∀ i j, HasDerivAt (fun ξ => dg (Function.update 0 j ξ) i) (H i j) 0) →
      (∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ‖x‖ ≤ Λ * ‖dg x‖) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (a : (Fin d → ℂ) → V) (S : ℝ),
        ContDiff ℝ (2 * d + 2 : ℕ) a → Function.support a ⊆ Metric.closedBall 0 r →
        (∀ j ≤ 2 * d + 2, ∀ x, ‖iteratedFDeriv ℝ j a x‖ ≤ S) →
        ∀ t : ℂ, t ≠ 0 → ‖t‖ ≤ 1 →
          ‖∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) -
              (psi β (g 0 / t) * ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • a 0‖ ≤ C * S * ‖t‖ ^ (d + 1) := by
  have hβpos : 0 < ‖β‖ := norm_pos_iff.2 hβ
  set δ : ℝ := r / ((d : ℝ) + 7) with hδdef
  have hδ : 0 < δ := by positivity
  set Γ : ℝ := ‖β‖ * (Λ * (max 1 δ⁻¹) ^ (d + 6)) with hΓdef
  have hΓ : 0 < Γ := by positivity
  set c₁ : ℝ := ‖β‖ / (2 * Λ) with hc₁def
  have hc₁ : 0 < c₁ := by positivity
  obtain ⟨ρ, hρ, _, CE, hE⟩ := real_core d β hβ r Γ c₁ hr hΓ hc₁
  have hΓH : 0 < Λ / (r / 2) / (r / 2) := by positivity
  obtain ⟨CD, hD⟩ := model d β hβ ρ (Λ / (r / 2) / (r / 2)) Λ hρ hΓH hΛ
  refine ⟨|CE| + |CD|, by positivity, ?_⟩
  intro g dg H hg hb hdg hdg0 hH hgrad V _ _ _ a S ha hsupp hS t ht ht1
  have hτ : 0 < ‖t‖ := norm_pos_iff.2 ht
  have hc0 : F_c β t ≠ 0 := by rw [← norm_pos_iff, F_c_norm β ht]; exact hβpos
  have h00 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (5 * r / 4) := Metric.mem_ball_self (by positivity)
  have h02 : (0 : Fin d → ℂ) ∈ Metric.ball (0 : Fin d → ℂ) (2 * r) := Metric.mem_ball_self (by positivity)
  have ha0 : ‖a 0‖ ≤ S := by simpa using hS 0 (Nat.zero_le _) 0
  have hS0 : 0 ≤ S := (norm_nonneg _).trans ha0

  have hφbd : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∀ i : ℕ, i ≤ d + 6 →
      ‖iteratedFDeriv ℝ i (F_phi d r (F_c β t) g) x‖ ≤ Γ := by
    intro x hx i hi
    have hi' : ((i + 1 : ℕ) : ℝ) * δ ≤ r := by
      have h1 : ((i + 1 : ℕ) : ℝ) ≤ (d : ℝ) + 7 := by
        have : i + 1 ≤ d + 7 := by omega
        exact_mod_cast this
      rw [hδdef]
      calc ((i + 1 : ℕ) : ℝ) * (r / ((d : ℝ) + 7)) ≤ ((d : ℝ) + 7) * (r / ((d : ℝ) + 7)) := by gcongr
        _ = r := by field_simp
    have h1 := F_phi_bound hr hg hb (F_c β t) hx i hδ hi'
    rw [F_c_norm β ht] at h1
    refine h1.trans ?_
    rw [hΓdef]
    have h2 : Λ / δ ^ i ≤ Λ * (max 1 δ⁻¹) ^ (d + 6) := by
      rw [div_eq_mul_inv, ← inv_pow]
      have h3 : δ⁻¹ ^ i ≤ (max 1 δ⁻¹) ^ i := pow_le_pow_left₀ (by positivity) (le_max_right _ _) i
      have h4 : (max 1 δ⁻¹) ^ i ≤ (max 1 δ⁻¹) ^ (d + 6) := pow_le_pow_right₀ (le_max_left _ _) hi
      gcongr
      exact h3.trans h4
    gcongr
  have hφ0 : fderiv ℝ (F_phi d r (F_c β t) g) 0 = 0 := by
    ext v
    rw [F_phi_fderiv hr hg _ h00, F_clm_sum]
    simp [F_dg_eq hg hdg h02, hdg0]
  have hlow : ∀ x ∈ Metric.closedBall (0 : Fin d → ℂ) r, ∃ l : Fin d × Bool,
      c₁ * ‖x‖ ≤ |fderiv ℝ (F_phi d r (F_c β t) g) x (dirv l)| := by
    intro x hx
    have := F_lower hd hr hΛ hg hdg hgrad hc0 hx
    rwa [F_c_norm β ht] at this
  have hmain := hE (F_phi d r (F_c β t) g) ‖t‖ hτ ht1 (F_phi_contDiff hr hg _ (d + 6)) hφbd hφ0 hlow V a S ha hsupp hS
  have hmod := hD H (F_H_symm hr hg hdg hH) (F_H_bound hr hg hb hdg hH) (F_H_lower hr hg hdg hdg0 hH hgrad) t ht ht1

  have hint1 : ∫ x : Fin d → ℂ, psi β (g x / t) • a x ∂(muPi β (Fin d)) =
      ∫ x, osc (F_phi d r (F_c β t) g) ‖t‖ x • a x ∂(muPi β (Fin d)) := by
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    by_cases hx : x ∈ Metric.closedBall (0 : Fin d → ℂ) r
    · simp only [F_osc_phi hr β ht hx]
    · have : a x = 0 := by
        by_contra h
        exact hx (hsupp h)
      simp only [this, smul_zero]
  have hint2 : ∫ x, osc (quad (F_phi d r (F_c β t) g)) ‖t‖ x * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d)) =
      psi β (g 0 / t) *
        ∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [F_osc_quad hr hg hdg hH β ht x, mul_assoc]
  rw [hint1]
  rw [hint2] at hmain
  set I1 := ∫ x, osc (F_phi d r (F_c β t) g) ‖t‖ x • a x ∂(muPi β (Fin d))
  set J := ∫ x : Fin d → ℂ, psi β ((x ⬝ᵥ (H *ᵥ x)) / (2 * t)) * ((cutB d ρ x : ℝ) : ℂ) ∂(muPi β (Fin d))
  have hsplit : I1 - (psi β (g 0 / t) * ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)) • a 0 =
      (I1 - (psi β (g 0 / t) * J) • a 0) +
        (psi β (g 0 / t) * (J - ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ))) • a 0 := by
    rw [mul_sub, sub_smul]; abel
  rw [hsplit]
  have hpw : 0 ≤ ‖t‖ ^ (d + 1) := by positivity
  have hsecond : ‖(psi β (g 0 / t) * (J - ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ))) • a 0‖ ≤ |CD| * S * ‖t‖ ^ (d + 1) := by
    rw [norm_smul, norm_mul, F_norm_psi, one_mul]
    calc ‖J - ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ)‖ * ‖a 0‖ ≤ (|CD| * ‖t‖ ^ (d + 1)) * S := by
          refine mul_le_mul (hmod.trans ?_) ha0 (norm_nonneg _) (by positivity)
          gcongr
          exact le_abs_self _
      _ = |CD| * S * ‖t‖ ^ (d + 1) := by ring
  have hfirst : ‖I1 - (psi β (g 0 / t) * J) • a 0‖ ≤ |CE| * S * ‖t‖ ^ (d + 1) := by
    refine hmain.trans ?_
    gcongr
    exact le_abs_self _
  calc _ ≤ ‖I1 - (psi β (g 0 / t) * J) • a 0‖ +
        ‖(psi β (g 0 / t) * (J - ((‖t‖ ^ d / ‖H.det‖ : ℝ) : ℂ))) • a 0‖ := norm_add_le _ _
    _ ≤ |CE| * S * ‖t‖ ^ (d + 1) + |CD| * S * ‖t‖ ^ (d + 1) := add_le_add hfirst hsecond
    _ = (|CE| + |CD|) * S * ‖t‖ ^ (d + 1) := by ring
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
