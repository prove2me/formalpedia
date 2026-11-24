-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.osc_bound
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:50:29.883809+00:00
-- url     : https://prove2.me/submissions/b19cb903-efb8-4322-9ce6-7692a0fd0eeb

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_isAddHaar_muPi
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_weight
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_norm_osc
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_reduce
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_B_norm_dirv

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
theorem _root_.solution (d q : ℕ) (β : ℂ) (hβ : β ≠ 0) (Γ c₁ : ℝ) (hc₁ : 0 < c₁) : ∃ C : ℝ, 0 ≤ C ∧
    ∀ (A : Set (Fin d → ℂ)) (φ : (Fin d → ℂ) → ℝ) (τ : ℝ), 0 < τ →
      ContDiff ℝ (d + 2 + q : ℕ) φ →
      Sym A (wt (Real.sqrt τ)) 1 (d + 1 + q) Γ (fderiv ℝ φ) →
      (∀ x ∈ A, ∃ l : Fin d × Bool, c₁ * ‖x‖ ≤ |fderiv ℝ φ x (dirv l)|) →
      ∀ (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V] (b : (Fin d → ℂ) → V) (K : ℝ),
        0 ≤ K → HasCompactSupport b → tsupport b ⊆ A →
        Sym A (wt (Real.sqrt τ)) (2 * (q : ℤ)) (d + 1 + q) K b →
        ‖∫ x, osc φ τ x • b x ∂(muPi β (Fin d))‖ ≤ C * K * τ ^ (d + q) := by
  have := isAddHaar_muPi d β hβ
  have hmin : 0 < min (c₁ ^ 2) 1 := lt_min (by positivity) one_pos
  obtain ⟨C, hC0, hC⟩ := B_reduce (E := Fin d → ℂ) (μ := muPi β (Fin d)) (Fin d × Bool) (d + 1 + q) Γ
    (min (c₁ ^ 2) 1 / 2) (by positivity)
  obtain ⟨C₀, hC₀0, hC₀⟩ := B_weight d β hβ
  refine ⟨C * C₀, mul_nonneg hC0 hC₀0, ?_⟩
  intro A φ τ hτ hφ hφS hlow V _ _ _ b K hK hbs hbA hb
  set σ := Real.sqrt τ with hσdef
  have hσ : 0 < σ := Real.sqrt_pos.2 hτ
  have hσ2 : σ ^ 2 = τ := Real.sq_sqrt hτ.le
  have hw : ∀ x ∈ A, 0 < wt σ x := fun x _ => by unfold wt; positivity
  have hτw : ∀ x ∈ A, τ ≤ wt σ x ^ 2 := fun x _ => by
    unfold wt; nlinarith [norm_nonneg x]
  have hD : ∀ x ∈ A, min (c₁ ^ 2) 1 / 2 * wt σ x ^ 2 ≤ ∑ l, (fderiv ℝ φ x (dirv l)) ^ 2 + τ := fun x hx => by
    obtain ⟨l, hl⟩ := hlow x hx
    have h1 : (c₁ * ‖x‖) ^ 2 ≤ (fderiv ℝ φ x (dirv l)) ^ 2 := by
      rw [← sq_abs (fderiv ℝ φ x (dirv l))]
      exact pow_le_pow_left₀ (by positivity) hl 2
    have h2 : (fderiv ℝ φ x (dirv l)) ^ 2 ≤ ∑ l, (fderiv ℝ φ x (dirv l)) ^ 2 :=
      Finset.single_le_sum (f := fun l => (fderiv ℝ φ x (dirv l)) ^ 2) (fun i _ => sq_nonneg _) (Finset.mem_univ l)
    have h3 : wt σ x ^ 2 ≤ 2 * (‖x‖ ^ 2 + σ ^ 2) := by
      unfold wt; nlinarith [sq_nonneg (‖x‖ - σ)]
    have h4 : min (c₁ ^ 2) 1 * ‖x‖ ^ 2 ≤ c₁ ^ 2 * ‖x‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_left _ _) (sq_nonneg _)
    have h5 : min (c₁ ^ 2) 1 * σ ^ 2 ≤ 1 * σ ^ 2 :=
      mul_le_mul_of_nonneg_right (min_le_right _ _) (sq_nonneg _)
    have h6 : min (c₁ ^ 2) 1 / 2 * wt σ x ^ 2 ≤ min (c₁ ^ 2) 1 / 2 * (2 * (‖x‖ ^ 2 + σ ^ 2)) :=
      mul_le_mul_of_nonneg_left h3 (by positivity)
    nlinarith
  obtain ⟨b', hb's, hb'A, hb'S, hEq⟩ := hC dirv B_norm_dirv A (wt σ) φ τ hτ hw hτw
    (hφ.of_le (by norm_cast; omega)) hφS hD V b (2 * (q : ℤ)) K hbs hbA hb
  rw [hEq]
  obtain ⟨hInt, hle⟩ := hC₀ σ hσ
  have hK' : 0 ≤ C * τ ^ (d + 1 + q) * K := by positivity
  have hbd : ∀ x, ‖osc φ τ x • b' x‖ ≤ C * τ ^ (d + 1 + q) * K * wt σ x ^ (-(2 * (d : ℤ) + 2)) := fun x => by
    rw [norm_smul, B_norm_osc, one_mul]
    by_cases hx : x ∈ A
    · have h := hb'S.2 x hx 0 le_rfl
      rw [norm_iteratedFDeriv_zero] at h
      convert h using 3
      push_cast
      ring
    · rw [image_eq_zero_of_notMem_tsupport (fun h => hx (hb'A h)), norm_zero]
      have : 0 < wt σ x := by unfold wt; positivity
      positivity
  calc ‖∫ x, osc φ τ x • b' x ∂(muPi β (Fin d))‖
      ≤ ∫ x, C * τ ^ (d + 1 + q) * K * wt σ x ^ (-(2 * (d : ℤ) + 2)) ∂(muPi β (Fin d)) :=
        norm_integral_le_of_norm_le (hInt.const_mul _) (Eventually.of_forall hbd)
    _ = C * τ ^ (d + 1 + q) * K * ∫ x, wt σ x ^ (-(2 * (d : ℤ) + 2)) ∂(muPi β (Fin d)) := integral_const_mul _ _
    _ ≤ C * τ ^ (d + 1 + q) * K * (C₀ / σ ^ 2) := mul_le_mul_of_nonneg_left hle hK'
    _ = C * C₀ * K * τ ^ (d + q) := by
        rw [hσ2, show d + 1 + q = (d + q) + 1 by ring, pow_succ]
        field_simp
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
