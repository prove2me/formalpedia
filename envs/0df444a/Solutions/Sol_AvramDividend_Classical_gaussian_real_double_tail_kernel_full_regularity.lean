-- Prove2me | solution 1 for AvramDividend.Classical.gaussian_real_double_tail_kernel_full_regularity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-24T08:20:18.437343+00:00
-- url     : https://prove2.me/submissions/0fefc89e-84d7-4d6a-890e-97893f5fd000

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_integrable
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_continuous_positive
import Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_real_kernel_antitone_positive
import Mathlib.Analysis.Complex.Exponential
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical MeasureTheory Set
open scoped ENNReal

theorem solution
    (μ : Measure ℝ) [SFinite μ] (φ : ℝ) (hφ : 0 < φ)
    (hlevy : (∫⁻ z in Ioi (0 : ℝ),
      ENNReal.ofReal (min 1 (z ^ 2)) ∂μ) < ⊤) :
    ∃ K : ℝ → ℝ,
      K = (fun t : ℝ => (∫⁻ z : ℝ, (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ).toReal) ∧
      Integrable K volume ∧
      ContinuousOn K (Ioi (0 : ℝ)) ∧
      AntitoneOn K (Ioi (0 : ℝ)) ∧
      (∀ t : ℝ, 0 < t → 0 ≤ K t) := by
  refine ⟨(fun t : ℝ => (∫⁻ z : ℝ, (if 0 < t ∧ t < z then ENNReal.ofReal (z - t) * ENNReal.ofReal (Real.exp (-(φ * z))) else 0) ∂μ).toReal), rfl, ?_, ?_, ?_, ?_⟩
  · exact gaussian_double_tail_real_kernel_integrable μ φ hφ hlevy
  · intro t ht
    simpa only [neg_mul] using
      (gaussian_double_tail_real_kernel_continuous_positive
        μ φ hφ hlevy t ht).continuousWithinAt
  · simpa only [neg_mul] using
      gaussian_double_tail_real_kernel_antitone_positive μ φ hφ hlevy
  · intro t ht
    exact ENNReal.toReal_nonneg
