-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_a436_integral_square_eq_lintegral_nnnorm_square
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T00:21:33.983814+00:00
-- url     : https://prove2.me/submissions/672ff15b-9418-474b-9de1-8c5ffae2cdbe

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory ENNReal Filter
open scoped NNReal ENNReal
noncomputable section

theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {μ : Measure Ω}
    (f : Ω → ℝ) (hf : Integrable (fun ω => (f ω)^2) μ) :
    (∫ ω, (f ω)^2 ∂μ) =
      (∫⁻ ω, (‖f ω‖₊ : ℝ≥0∞)^2 ∂μ).toReal := by
  have hn : ∀ᵐ ω ∂μ, 0 ≤ (f ω)^2 :=
    Filter.Eventually.of_forall fun ω => sq_nonneg _
  rw [integral_eq_lintegral_of_nonneg_ae hn hf.aestronglyMeasurable]
  congr 1
  apply lintegral_congr
  intro ω
  rw [← sq_abs (f ω), ENNReal.ofReal_pow (abs_nonneg _) 2,
    ← Real.enorm_eq_ofReal_abs]
  rfl
