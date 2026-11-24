-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.ae_equality_from_test_functions
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-3
-- created : 2026-11-24T17:11:07.163998+00:00
-- url     : https://prove2.me/submissions/73700091-77a5-4fff-9410-268a12c7b2aa

import Definitions.Def_Formalism_HermitianCurvature_StatementB
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_AeEqualityFromTestFunctions
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_measurableSet_Quad
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_test_prod_zero
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_test_prod_measurable
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_ae_eq_of_tests
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_lintegral_test_restrict
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_integrable_test
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_lintegral_test_cont
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_contOn_pos
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_contOn_neg
import Theorems.Thm_Formalism_FourierDecayAlt_P_B3_integral_test_parts

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P
open Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.P.B3
namespace Formalism.FourierDecayAlt.P
theorem _root_.solution : Formalism.FourierDecayAlt.B.AeFromTests := by
  intro b c hb hc H
  have hre : ContinuousOn (fun τ => (c τ).re) Quad := Complex.continuous_re.comp_continuousOn hc
  have him : ContinuousOn (fun τ => (c τ).im) Quad := Complex.continuous_im.comp_continuousOn hc
  have mO : ∀ h : ℝ × ℝ → ℝ, ContinuousOn h Quad →
      AEMeasurable (fun τ => ENNReal.ofReal (h τ)) (volume.restrict Quad) := fun h hh =>
    (hh.aemeasurable measurableSet_Quad).ennreal_ofReal

  have R : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
      (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ ∂(volume.restrict Quad)) ≠ ∞ ∧
      (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ ∂(volume.restrict Quad)).toReal =
        (∫ τ, w₁ τ.1 * w₂ τ.2 * (c τ).re ∂(volume.restrict Quad)) ∧
      (0 : ℝ) = ∫ τ, w₁ τ.1 * w₂ τ.2 * (c τ).im ∂(volume.restrict Quad) := by
    intro w₁ w₂ h₁ h₂ p₁ p₂
    obtain ⟨hfin, heq⟩ := H w₁ w₂ h₁ h₂ p₁ p₂
    rw [lintegral_test_restrict h₁ h₂ b] at hfin heq
    have hint : Integrable (fun τ : ℝ × ℝ => ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * c τ) (volume.restrict Quad) := by
      simpa only [Complex.real_smul] using integrable_test h₁ h₂ hc
    have hres : (∫ τ : ℝ × ℝ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * c τ) =
        ∫ τ, ((w₁ τ.1 * w₂ τ.2 : ℝ) : ℂ) * c τ ∂(volume.restrict Quad) := by
      refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun τ hτ => ?_).symm
      rw [test_prod_zero h₁ h₂ hτ]
      simp
    rw [hres] at heq
    refine ⟨hfin, ?_, ?_⟩
    · have := congrArg Complex.re heq
      rw [Complex.ofReal_re] at this
      rw [this, ← Complex.reCLM_apply, ← Complex.reCLM.integral_comp_comm hint]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [Complex.reCLM_apply, Complex.re_ofReal_mul]
    · have := congrArg Complex.im heq
      rw [Complex.ofReal_im] at this
      rw [this, ← Complex.imCLM_apply, ← Complex.imCLM.integral_comp_comm hint]
      refine integral_congr_ae (Eventually.of_forall fun τ => ?_)
      simp only [Complex.imCLM_apply, Complex.im_ofReal_mul]

  have split : ∀ w₁ w₂ : ℝ → ℝ, IsTest w₁ → IsTest w₂ → (∀ x, 0 ≤ w₁ x) → (∀ x, 0 ≤ w₂ x) →
      (∫⁻ τ, ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * (b τ + ENNReal.ofReal (max (-(c τ).re) 0))
        ∂(volume.restrict Quad)) =
        ENNReal.ofReal (∫ τ, w₁ τ.1 * w₂ τ.2 * max (c τ).re 0 ∂(volume.restrict Quad)) := by
    intro w₁ w₂ h₁ h₂ p₁ p₂
    obtain ⟨hfin, h1, -⟩ := R w₁ w₂ h₁ h₂ p₁ p₂
    have hm : AEMeasurable (fun τ : ℝ × ℝ => ENNReal.ofReal (w₁ τ.1 * w₂ τ.2) * b τ) (volume.restrict Quad) :=
      (test_prod_measurable h₁ h₂).aemeasurable.mul hb
    simp only [mul_add]
    rw [lintegral_add_left' hm,
      lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_neg hre) (fun τ => le_max_right _ _),
      ← ENNReal.ofReal_toReal hfin, ← ENNReal.ofReal_add ENNReal.toReal_nonneg
        (integral_nonneg fun τ => mul_nonneg (mul_nonneg (p₁ _) (p₂ _)) (le_max_right _ _)),
      h1, integral_test_parts h₁ h₂ hre]
    congr 1
    ring
  have A : (fun τ => b τ + ENNReal.ofReal (max (-(c τ).re) 0)) =ᵐ[volume.restrict Quad]
      fun τ => ENNReal.ofReal (max (c τ).re 0) := by
    refine ae_eq_of_tests (hb.add (mO _ (contOn_neg hre))) (mO _ (contOn_pos hre)) ?_ ?_
    · intro w₁ w₂ h₁ h₂ p₁ p₂
      rw [split w₁ w₂ h₁ h₂ p₁ p₂]
      exact ENNReal.ofReal_ne_top
    · intro w₁ w₂ h₁ h₂ p₁ p₂
      rw [split w₁ w₂ h₁ h₂ p₁ p₂, lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_pos hre) (fun τ => le_max_right _ _)]

  have B : (fun τ => ENNReal.ofReal (max (c τ).im 0)) =ᵐ[volume.restrict Quad]
      fun τ => ENNReal.ofReal (max (-(c τ).im) 0) := by
    refine ae_eq_of_tests (mO _ (contOn_pos him)) (mO _ (contOn_neg him)) ?_ ?_
    · intro w₁ w₂ h₁ h₂ p₁ p₂
      rw [lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_pos him) (fun τ => le_max_right _ _)]
      exact ENNReal.ofReal_ne_top
    · intro w₁ w₂ h₁ h₂ p₁ p₂
      obtain ⟨-, -, h2⟩ := R w₁ w₂ h₁ h₂ p₁ p₂
      rw [lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_pos him) (fun τ => le_max_right _ _),
        lintegral_test_cont h₁ h₂ p₁ p₂ (contOn_neg him) (fun τ => le_max_right _ _)]
      congr 1
      rw [integral_test_parts h₁ h₂ him] at h2
      linarith
  filter_upwards [A, B] with τ hA hB
  have hbt : b τ ≠ ∞ := by
    intro h
    rw [h, top_add] at hA
    exact ENNReal.ofReal_ne_top hA.symm
  have h1 : (b τ).toReal + max (-(c τ).re) 0 = max (c τ).re 0 := by
    have := congrArg ENNReal.toReal hA
    rwa [ENNReal.toReal_add hbt ENNReal.ofReal_ne_top, ENNReal.toReal_ofReal (le_max_right _ _),
      ENNReal.toReal_ofReal (le_max_right _ _)] at this
  have h2 : max (c τ).im 0 = max (-(c τ).im) 0 :=
    (ENNReal.ofReal_eq_ofReal_iff (le_max_right _ _) (le_max_right _ _)).mp hB
  have e1 := max_zero_sub_max_neg_zero_eq_self (c τ).re
  have e2 := max_zero_sub_max_neg_zero_eq_self (c τ).im
  refine ⟨hbt, Complex.ext ?_ ?_⟩
  · rw [Complex.ofReal_re]
    linarith
  · rw [Complex.ofReal_im]
    linarith
end Formalism.FourierDecayAlt.P
