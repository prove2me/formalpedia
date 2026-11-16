-- Prove2me | solution 1 for AvramDividend.Classical.avram_b29_product_brownian_centered_restricted_nojump_gain_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-15T15:15:42.451508+00:00
-- url     : https://prove2.me/submissions/0652dacf-5027-4410-aade-837fdf805528

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_b29_centered_gaussian_coordinate_product_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_b29_product_event_independent_centered_physical_gain
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set ProbabilityTheory AvramDividend.Classical
open scoped ENNReal

theorem solution
    {ΩB ΩN : Type*} [mB : MeasurableSpace ΩB]
    [mN : MeasurableSpace ΩN]
    (μ : Measure ΩB) (ν : Measure ΩN)
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (A : Set ΩN) (hA : MeasurableSet A)
    (H : ℕ → ΩB → ℝ) (hHm : ∀ k, Measurable (H k))
    (hHI : ∀ k, Integrable (H k) μ)
    (hZero : ∀ k, (∫ ω, H k ω ∂μ) = 0)
    (G : ℕ → ΩB × ΩN → ℝ)
    (hSame : ∀ k, ∀ᵐ p ∂((μ.prod ν).restrict {p : ΩB × ΩN | p.2 ∈ A}),
      G k p = H k p.1) :
    ∀ k, (∫ p in {p : ΩB × ΩN | p.2 ∈ A},
      G k p ∂(μ.prod ν)) = 0 := by
  obtain ⟨hProdInt, hProdMean⟩ :=
    avram_b29_centered_gaussian_coordinate_product_mean_zero
      μ ν H hHI hZero
  exact
    avram_b29_product_event_independent_centered_physical_gain
      μ ν A hA H hHm G hProdInt hSame hProdMean
