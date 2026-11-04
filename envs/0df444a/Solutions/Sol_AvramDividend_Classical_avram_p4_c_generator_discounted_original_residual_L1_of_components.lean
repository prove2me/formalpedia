-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_c_generator_discounted_original_residual_L1_of_components
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T21:42:37.563475+00:00
-- url     : https://prove2.me/submissions/6524eebe-86ac-4386-a07a-90224d33933b

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Reconstruct the discounted original Levy generator-minus-discount L¹
residual from three physically justified finite-clock integrable pieces. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {T : Type*} [mT : MeasurableSpace T]
    (μ : Measure T) (R : T → ℝ) (clock : T → ℝ≥0)
    (w : ℝ → ℝ) (q : ℝ) (A : Set T)
    (hcont : Integrable (A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) *
        (X.σ ^ 2 / 2 * iteratedDeriv 2 w (R t) +
          X.c * deriv w (R t)))) μ)
    (hjump : Integrable (A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) *
        (∫ z in Iio (0 : ℝ),
          SpectrallyNegativeLevy.generatorIntegrand w (R t) z ∂X.ν))) μ)
    (hpay : Integrable (A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) * w (R t))) μ) :
    Integrable (A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) *
        (X.generator w (R t) - q * w (R t)))) μ := by
  have hEq : A.indicator (fun t =>
      Real.exp (-(q * (clock t : ℝ))) *
        (X.generator w (R t) - q * w (R t))) =
      (fun t =>
        A.indicator (fun s =>
          Real.exp (-(q * (clock s : ℝ))) *
            (X.σ ^ 2 / 2 * iteratedDeriv 2 w (R s) +
              X.c * deriv w (R s))) t +
        A.indicator (fun s =>
          Real.exp (-(q * (clock s : ℝ))) *
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w (R s) z ∂X.ν)) t -
        q * A.indicator (fun s =>
          Real.exp (-(q * (clock s : ℝ))) * w (R s)) t) := by
    funext t
    by_cases ht : t ∈ A
    · simp only [Set.indicator_of_mem ht]
      change Real.exp (-(q * (clock t : ℝ))) *
          ((X.σ ^ 2 / 2 * iteratedDeriv 2 w (R t) +
            X.c * deriv w (R t) +
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w (R t) z ∂X.ν)) -
            q * w (R t)) =
          Real.exp (-(q * (clock t : ℝ))) *
            (X.σ ^ 2 / 2 * iteratedDeriv 2 w (R t) +
              X.c * deriv w (R t)) +
          Real.exp (-(q * (clock t : ℝ))) *
            (∫ z in Iio (0 : ℝ),
              SpectrallyNegativeLevy.generatorIntegrand w (R t) z ∂X.ν) -
          q * (Real.exp (-(q * (clock t : ℝ))) * w (R t))
      ring
    · simp only [Set.indicator_of_notMem ht]
      ring
  rw [hEq]
  exact (hcont.add hjump).sub (hpay.const_mul q)
