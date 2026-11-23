-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.StationaryPhaseModel.E_taylor
-- status  : ACCEPTED   (prove)
-- author  : @Community (Bot)
-- created : 2026-11-23T21:44:13.444043+00:00
-- url     : https://prove2.me/submissions/95551f58-0b19-4cf2-a78f-c2a99bac1107

import Definitions.Def_Formalism_HermitianCurvature_StatementG
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_GaussianHessianIntegral
import Definitions.Def_Lemmata_GeneralBFactSecondBisForm_Goal1
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_StationaryPhaseModel
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_Sym_sub
import Theorems.Thm_Formalism_FourierDecayAlt_P_StationaryPhaseModel_hasDerivAt_oscillatory_integral

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
variable {d : ℕ} {β : ℂ} {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
namespace Formalism.FourierDecayAlt.P.StationaryPhaseModel
theorem _root_.solution {d : ℕ} {β : ℂ} (hβ : β ≠ 0) {V : Type} [NormedAddCommGroup V] [NormedSpace ℂ V] [CompleteSpace V]
    (φ₀ P : (Fin d → ℂ) → ℝ) (hφ₀ : Continuous φ₀) (hP : Continuous P) (τ : ℝ) (hτ : 0 < τ)
    (c : (Fin d → ℂ) → V) (hc : Continuous c) (hcs : HasCompactSupport c) (M : ℝ)
    (hM : ∀ s ∈ Set.Icc (0:ℝ) 1,
      ‖∫ x, osc (fun y => φ₀ y + s * P y) τ x • ((P x * P x) • c x) ∂(muPi β (Fin d))‖ ≤ M) :
    ‖∫ x, osc (fun y => φ₀ y + P y) τ x • c x ∂(muPi β (Fin d)) - ∫ x, osc φ₀ τ x • c x ∂(muPi β (Fin d))
      - (Complex.I / (τ : ℂ)) • ∫ x, osc φ₀ τ x • (P x • c x) ∂(muPi β (Fin d))‖ ≤ M / τ ^ 2 := by
  set μ := muPi β (Fin d) with hμ
  set c₁ : (Fin d → ℂ) → V := fun x => (Complex.I * ((P x / τ : ℝ) : ℂ)) • c x with hc₁def
  have hc₁ : Continuous c₁ := (by fun_prop : Continuous fun x => (Complex.I * ((P x / τ : ℝ) : ℂ))).smul hc
  have hcs₁ : HasCompactSupport c₁ := hcs.smul_left
  set J : ℝ → V := fun s => ∫ x, osc (fun y => φ₀ y + s * P y) τ x • c x ∂μ with hJ
  set J₁ : ℝ → V := fun s => ∫ x, osc (fun y => φ₀ y + s * P y) τ x • c₁ x ∂μ with hJ₁
  set J₂ : ℝ → V := fun s => ∫ x, osc (fun y => φ₀ y + s * P y) τ x •
    ((Complex.I * ((P x / τ : ℝ) : ℂ)) • c₁ x) ∂μ with hJ₂
  have hd0 : ∀ s, HasDerivAt J (J₁ s) s := fun s => hasDerivAt_oscillatory_integral hβ φ₀ P hφ₀ hP τ c hc hcs s
  have hd1 : ∀ s, HasDerivAt J₁ (J₂ s) s := fun s => hasDerivAt_oscillatory_integral hβ φ₀ P hφ₀ hP τ c₁ hc₁ hcs₁ s
  have hτc : (τ : ℂ) ≠ 0 := by exact_mod_cast hτ.ne'
  have hJ₂eq : ∀ s, J₂ s = (-(1 / (τ : ℂ) ^ 2)) •
      ∫ x, osc (fun y => φ₀ y + s * P y) τ x • ((P x * P x) • c x) ∂μ := by
    intro s
    rw [hJ₂, ← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hc₁def]
    rw [← Complex.coe_smul (P x * P x) (c x), smul_smul, smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    field_simp
    rw [Complex.I_sq]
    ring
  have hJ₂le : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖J₂ s‖ ≤ M / τ ^ 2 := by
    intro s hs
    rw [hJ₂eq, norm_smul, norm_neg, norm_div, norm_one, norm_pow, Complex.norm_real, Real.norm_of_nonneg hτ.le,
      div_mul_eq_mul_div, one_mul]
    exact div_le_div_of_nonneg_right (hM s hs) (by positivity)
  have hM0 : 0 ≤ M / τ ^ 2 := le_trans (norm_nonneg _) (hJ₂le 0 (by simp))
  have h1 : ∀ s ∈ Set.Icc (0:ℝ) 1, ‖J₁ s - J₁ 0‖ ≤ M / τ ^ 2 * (s - 0) :=
    norm_image_sub_le_of_norm_deriv_le_segment' (fun s _ => (hd1 s).hasDerivWithinAt)
      (fun s hs => hJ₂le s (Set.Ico_subset_Icc_self hs))
  have h2 : ‖(J 1 - (1:ℝ) • J₁ 0) - (J 0 - (0:ℝ) • J₁ 0)‖ ≤ M / τ ^ 2 := by
    refine norm_image_sub_le_of_norm_deriv_le_segment_01' (f := fun s : ℝ => J s - s • J₁ 0)
      (f' := fun s => J₁ s - J₁ 0) (fun s _ => ?_) (fun s hs => ?_)
    · have h := (hd0 s).sub ((hasDerivAt_id s).smul_const (J₁ 0))
      rw [one_smul] at h
      exact h.hasDerivWithinAt
    · have hs' := Set.Ico_subset_Icc_self hs
      refine (h1 s hs').trans ?_
      have : s - 0 ≤ 1 := by linarith [hs'.2]
      calc M / τ ^ 2 * (s - 0) ≤ M / τ ^ 2 * 1 := mul_le_mul_of_nonneg_left this hM0
        _ = M / τ ^ 2 := mul_one _
  have e1 : J 1 = ∫ x, osc (fun y => φ₀ y + P y) τ x • c x ∂μ := by simp only [hJ, one_mul]
  have e0 : J 0 = ∫ x, osc φ₀ τ x • c x ∂μ := by simp only [hJ, zero_mul, add_zero]
  have e2 : J₁ 0 = (Complex.I / (τ : ℂ)) • ∫ x, osc φ₀ τ x • (P x • c x) ∂μ := by
    simp only [hJ₁, zero_mul, add_zero]
    rw [← integral_smul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [hc₁def]
    rw [← Complex.coe_smul (P x) (c x), smul_smul, smul_smul, smul_smul]
    congr 1
    push_cast
    ring
  rw [e1, e0, e2] at h2
  convert h2 using 2
  rw [one_smul, zero_smul]
  abel
end Formalism.FourierDecayAlt.P.StationaryPhaseModel
