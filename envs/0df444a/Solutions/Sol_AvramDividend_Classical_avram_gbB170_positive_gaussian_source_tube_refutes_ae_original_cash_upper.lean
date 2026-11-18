-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB170_positive_gaussian_source_tube_refutes_ae_original_cash_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:11:38.519748+00:00
-- url     : https://prove2.me/submissions/f28a5602-ff00-4f29-8fcf-3b31520211df

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB166_original_centered_gaussian_strict_cash_excess_with_bounded_noise
import Theorems.Thm_AvramDividend_Classical_avram_gbB169_positive_tube_prevents_ae_fixedband_upper
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- A positive original Gaussian tube makes the false fixed-band upper fail almost everywhere. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (A : Set Ω) (hA : MeasurableSet A) (hApos : 0 < P A)
    (B : Ω → ℝ≥0 → ℝ)
    (hSource : ∀ ω ∈ A, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B ω s + 2 * (s : ℝ))
    (hCentered : ∀ ω ∈ A, ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B ω s| ≤ (1 / 4000 : ℝ))
    (N : Ω → ℝ)
    (hN : ∀ᵐ ω ∂(P.restrict A), |N ω| ≤ (1 / 4000 : ℝ)) :
    ¬ (∀ᵐ ω ∂(P.restrict A), (Real.exp (-(1 / 100000 : ℝ)) *
         (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
       (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal) -
         (3 / 16 : ℝ) ≤ N ω + (1 / 1936 : ℝ)) := by
  apply avram_gbB169_positive_tube_prevents_ae_fixedband_upper P A hApos
  filter_upwards [ae_restrict_mem hA, hN] with ω hω hNω
  exact avram_gbB166_original_centered_gaussian_strict_cash_excess_with_bounded_noise
    X ω (B ω) (hSource ω hω) (hCentered ω hω) (N ω) hNω
