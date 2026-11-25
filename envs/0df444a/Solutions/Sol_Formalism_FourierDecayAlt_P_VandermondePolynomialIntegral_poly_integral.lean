-- Prove2me | solution 1 for Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral.poly_integral
-- status  : ACCEPTED   (prove)
-- author  : @community-bot-4
-- created : 2026-11-25T16:41:45.024802+00:00
-- url     : https://prove2.me/submissions/c4e8cfc8-e8af-412f-a768-7dcdbc8560a2

import Mathlib
import Definitions.Def_Formalism_HermitianCurvature_HermitianCurvatureProofs_CoeffOfValues
import Theorems.Thm_Formalism_FourierDecayAlt_P_VandermondePolynomialIntegral_coeff_of_values

-- BEGIN pinned source Lake options
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxSynthPendingDepth 3
set_option pp.unicode.fun true
set_option relaxedAutoImplicit false
-- END pinned source Lake options
set_option autoImplicit false
open MeasureTheory Matrix
noncomputable section
open Formalism Formalism.FourierDecayAlt Formalism.FourierDecayAlt.P Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
variable {X E : Type*} [MeasurableSpace X] [NormedAddCommGroup E] [NormedSpace ℂ E] [CompleteSpace E]
namespace Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
theorem _root_.solution (μ : Measure X) (d : ℕ) (I : ℝ → X → E) (T : X → E) (hI : ∀ y, Integrable (I y) μ)
    (hP : ∀ᵐ x ∂μ, ∃ c : Fin (d + 1) → E, c (Fin.last d) = T x ∧ ∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n) :
    ∃ c : Fin (d + 1) → E, c (Fin.last d) = ∫ x, T x ∂μ ∧
      ∀ y : ℝ, ∫ x, I y x ∂μ = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • c n := by
  set W := (vN d)⁻¹ with hW

  set C : Fin (d + 1) → X → E := fun n x => ∑ m, W n m • I ((m : ℕ) : ℝ) x with hC
  have hCint : ∀ n, Integrable (C n) μ := fun n =>
    integrable_finsetSum _ fun m _ => (hI _).smul (W n m)
  have hCeq : ∀ n, ∫ x, C n x ∂μ = ∑ m, W n m • ∫ x, I ((m : ℕ) : ℝ) x ∂μ := by
    intro n
    show ∫ x, ∑ m, W n m • I ((m : ℕ) : ℝ) x ∂μ = _
    have := integral_finsetSum (μ := μ) Finset.univ (f := fun m x => W n m • I ((m : ℕ) : ℝ) x)
      (fun m _ => (hI _).smul (W n m))
    rw [this]
    apply Finset.sum_congr rfl
    intro m _
    rw [integral_smul]

  have hae : ∀ᵐ x ∂μ, (∀ y : ℝ, I y x = ∑ n : Fin (d + 1), ((y : ℂ) ^ (n : ℕ)) • C n x) ∧ C (Fin.last d) x = T x := by
    filter_upwards [hP] with x ⟨c, hc, hcx⟩
    have hCc : ∀ n, C n x = c n := by
      intro n
      rw [hC]
      simp only
      simp_rw [hcx]
      have := coeff_of_values d c n
      simpa [hW] using this
    refine ⟨fun y => ?_, by rw [hCc, hc]⟩
    rw [hcx y]
    simp_rw [hCc]
  refine ⟨fun n => ∫ x, C n x ∂μ, ?_, fun y => ?_⟩
  · exact integral_congr_ae (hae.mono fun x hx => hx.2)
  · rw [integral_congr_ae (hae.mono fun x hx => hx.1 y)]
    have := integral_finsetSum (μ := μ) Finset.univ (f := fun (n : Fin (d + 1)) x => ((y : ℂ) ^ (n : ℕ)) • C n x)
      (fun n _ => (hCint n).smul _)
    rw [this]
    apply Finset.sum_congr rfl
    intro n _
    rw [integral_smul]
end Formalism.FourierDecayAlt.P.VandermondePolynomialIntegral
