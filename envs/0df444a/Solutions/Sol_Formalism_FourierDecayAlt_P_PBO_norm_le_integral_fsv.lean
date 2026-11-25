-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.PBO.norm_le_integral_fsv
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T17:02:46.31765+00:00
-- url     : https://prove2.me/submissions/169e71c9-970c-4f0d-b2d1-2fad8325f8d8

import Definitions.Def_Formalism_HermitianCurvature_CompositeFormulaLevelZero
import Mathlib.Analysis.Fourier.FourierTransform
import Mathlib.Analysis.Fourier.Inversion
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_NormLeIntegralFsv
import Theorems.Thm_Formalism_FourierDecayAlt_P_PBO_fsv_smul

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Real
open scoped FourierTransform RealInnerProductSpace ComplexConjugate
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.PBO
namespace Formalism.FourierDecayAlt.P.PBO
theorem _root_.solution (φ : ℂ → ℂ) (hφ : Continuous φ) (hi : MeasureTheory.Integrable φ)
    (hΞ : MeasureTheory.Integrable (fun s : ℂ => ∫ t : ℂ, P5.fsv s t * φ t)) (t : ℂ) :
    ‖φ t‖ ≤ ∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖ := by
  have hc : (π⁻¹ : ℝ) ≠ 0 := inv_ne_zero Real.pi_ne_zero
  have hL : ∀ s : ℂ, (∫ u : ℂ, P5.fsv s u * φ u) = 𝓕 φ ((π⁻¹ : ℝ) • isoQ s) := by
    intro s
    rw [fourier_eq]
    exact integral_congr_ae (Filter.Eventually.of_forall fun u => fsv_smul s u (φ u))
  have hmp : MeasurePreserving isoQ := isoQ.measurePreserving
  have hme : MeasurableEmbedding isoQ := isoQ.toHomeomorph.measurableEmbedding
  have hint1 : Integrable (fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) := by
    have h1 : Integrable ((fun s : ℂ => 𝓕 φ ((π⁻¹ : ℝ) • s)) ∘ isoQ) := by
      have h2 := hΞ
      simp_rw [hL] at h2
      exact h2
    exact (hmp.integrable_comp_emb hme).mp h1
  have hint : Integrable (𝓕 φ) := by
    first
      | exact (integrable_comp_smul_iff volume (𝓕 φ) hc).mp hint1
      | exact (MeasureTheory.integrable_comp_smul_iff (volume : Measure ℂ) (𝓕 φ) hc).mp hint1
      | exact (Integrable.comp_smul_iff hc).mp hint1
  have hinv : 𝓕⁻ (𝓕 φ) t = φ t := by
    first
      | exact hi.fourier_inversion hint hφ.continuousAt
      | exact hi.fourierInv_fourier_eq hint hφ.continuousAt
      | exact hφ.fourierInv_fourier_eq hi hint t
      | exact Continuous.fourierInv_fourier_eq hφ hi hint t
      | exact hi.fourierInv_fourier hint hφ.continuousAt
      | exact hφ.fourierInv_fourier hi hint t
      | exact MeasureTheory.Integrable.fourier_inversion hi hint hφ.continuousAt
  have hb : ‖φ t‖ ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := by
    rw [← hinv]
    first
      | rw [fourierInv_eq]
      | rw [Real.fourierInv_eq]
      | rw [fourierInv_eq']
      | rw [fourierInv_eq_fourier_neg, fourier_eq]
    refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
    congr 1
    funext w
    first
      | exact Circle.norm_smul _ _
      | simp
  have e1 := hmp.integral_comp hme (fun s : ℂ => ‖𝓕 φ ((π⁻¹ : ℝ) • s)‖)
  have e2 := Measure.integral_comp_smul (volume : Measure ℂ) (fun w : ℂ => ‖𝓕 φ w‖) (π⁻¹ : ℝ)
  try dsimp only at e1
  try dsimp only at e2
  have heq : (∫ s : ℂ, ‖∫ u : ℂ, P5.fsv s u * φ u‖) =
      |((π⁻¹ : ℝ) ^ 2)⁻¹| • ∫ w : ℂ, ‖𝓕 φ w‖ := by
    simp_rw [hL]
    rw [e1, e2, Complex.finrank_real_complex]
  rw [heq, smul_eq_mul]
  have h0 : 0 ≤ ∫ w : ℂ, ‖𝓕 φ w‖ := integral_nonneg fun _ => norm_nonneg _
  have hπ : 1 ≤ |((π⁻¹ : ℝ) ^ 2)⁻¹| := by
    rw [inv_pow, inv_inv, abs_of_pos (by positivity)]
    nlinarith [Real.pi_gt_three]
  nlinarith
end Formalism.FourierDecayAlt.P.PBO
