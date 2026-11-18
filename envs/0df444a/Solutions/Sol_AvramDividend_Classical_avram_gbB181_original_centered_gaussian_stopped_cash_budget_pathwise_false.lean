-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB181_original_centered_gaussian_stopped_cash_budget_pathwise_false
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T19:12:06.29793+00:00
-- url     : https://prove2.me/submissions/77805a3c-80b6-467a-9875-3a68e1ba8b77

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
import Theorems.Thm_AvramDividend_Classical_avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
import Theorems.Thm_AvramDividend_Classical_avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Actual original stopped Gaussian cash contradicts fixed-band bound on narrow tube. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSource : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ))
    (N : ℝ) (hN : |N| ≤ (1 / 4000 : ℝ)) :
    ¬ (Real.exp (-(1 / 100000 : ℝ)) *
      (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
      (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-( (1 / 100 : ℝ) * t )))
      ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal) -
      (3 / 16 : ℝ) ≤ N + (1 / 1936 : ℝ) := by
  have hTube :=
    avram_gbB156_centered_short_Brownian_tube_implies_original_source_tube
      X ω B hSource hCentered
  have hFinite :=
    avram_gbB163_original_equal_cap_barrier_finite_discounted_strict_stopped_cash
      X ω (1 / 1000 : ℝ≥0) (1 / 100 : ℝ) (by norm_num)
  exact
    avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
      X ω B hSource hCentered hTube hFinite N hN
