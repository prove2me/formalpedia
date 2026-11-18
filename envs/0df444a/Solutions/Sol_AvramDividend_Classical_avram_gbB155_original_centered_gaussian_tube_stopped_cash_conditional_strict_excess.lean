-- Prove2me | solution 1 for AvramDividend.Classical.avram_gbB155_original_centered_gaussian_tube_stopped_cash_conditional_strict_excess
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-17T18:50:57.250196+00:00
-- url     : https://prove2.me/submissions/d680ddcb-364d-4b69-a73e-5b107306d661

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_short_barrier_terminal_reserve_le_cap
import Theorems.Thm_AvramDividend_Classical_avram_gbB149_original_gaussian_barrier_dividends_quantitative_drift_lower
import Theorems.Thm_AvramDividend_Classical_avram_gbB150_original_gaussian_centered_tube_terminal_reserve_near_cap
import Theorems.Thm_AvramDividend_Classical_avram_gbB151_short_gaussian_cash_lower_and_noise_tube_strict_fixedband_excess
import Theorems.Thm_AvramDividend_Classical_avram_gbB154_original_gaussian_tube_strict_cash_real_lower_by_dividend_regulator
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory AvramDividend.Classical Set
open scoped NNReal ENNReal
noncomputable section
/-- Source-faithful direct stopped cash contradiction from a centered Gaussian tube. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (B : ℝ≥0 → ℝ)
    (hSource : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      X.X s ω = B s + 2 * (s : ℝ))
    (hCentered : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |B s| ≤ (1 / 4000 : ℝ))
    (hTube : ∀ s : ℝ≥0, s ≤ (1 / 1000 : ℝ≥0) →
      |X.X s ω| ≤ (1 / 400 : ℝ))
    (hFinite : (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)) ≠ ⊤)
    (N : ℝ) (hN : |N| ≤ (1 / 4000 : ℝ)) :
    ¬ (Real.exp (-(1 / 100000 : ℝ)) *
         (2 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) - 4 * (riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω) ^ 2) +
       (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω)).toReal) -
         (3 / 16 : ℝ) ≤ N + (1 / 1936 : ℝ) := by
  have hTpos : (0 : ℝ≥0) < (1 / 1000 : ℝ≥0) := by norm_num
  have hSpos : (0 : ℝ≥0) < (99 / 100000 : ℝ≥0) := by norm_num
  have hST : (99 / 100000 : ℝ≥0) < (1 / 1000 : ℝ≥0) := by norm_num
  let D := barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)
  let y := riskProcess X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) (1 / 1000 : ℝ≥0) ω
  let L : ℝ≥0∞ := (∫⁻ t in paymentTimes
      (ruinTime X (1 / 8 : ℝ) (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω) ∩ Iio ((1 / 1000 : ℝ≥0) : ℝ),
      ENNReal.ofReal (Real.exp (-((1 / 100 : ℝ) * t)))
        ∂(dividendMeasure (barrierStrategy X (1 / 8 : ℝ) (1 / 8 : ℝ)) ω))
  let F : ℝ := Real.exp (-(1 / 100000 : ℝ)) *
    (2 * y - 4 * y ^ 2) + L.toReal
  have hYraw :=
    avram_gbB150_original_gaussian_centered_tube_terminal_reserve_near_cap
      X (1 / 1000 : ℝ≥0) hTpos ω B hSource hCentered
  have hYlo : (249 / 2000 : ℝ) ≤ y := by
    convert hYraw using 1 <;> norm_num
  have hYhi : y ≤ (1 / 8 : ℝ) :=
    avram_gbB49_original_short_barrier_terminal_reserve_le_cap
      X (1 / 1000 : ℝ≥0) ω hTpos hTube
  have hDiv := avram_gbB149_original_gaussian_barrier_dividends_quantitative_drift_lower
    X (99 / 100000 : ℝ≥0) hSpos ω (B (99 / 100000 : ℝ≥0))
    (hSource (99 / 100000 : ℝ≥0) (le_of_lt hST))
    (hCentered (99 / 100000 : ℝ≥0) (le_of_lt hST))
  have hDivLo : (173 / 100000 : ℝ) ≤ D (99 / 100000 : ℝ≥0) ω := by
    convert hDiv using 1 <;> norm_num
  have hCash := avram_gbB154_original_gaussian_tube_strict_cash_real_lower_by_dividend_regulator
    X ω (99 / 100000 : ℝ≥0) (1 / 1000 : ℝ≥0) hST hTube (1 / 100 : ℝ) (by norm_num) hFinite
  have hexp : Real.exp (-((1 / 100 : ℝ) * ((99 / 100000 : ℝ≥0) : ℝ))) =
      Real.exp (-(99 / 10000000 : ℝ)) := by norm_num
  rw [hexp] at hCash
  have hF : Real.exp (-(99 / 10000000 : ℝ)) * D (99 / 100000 : ℝ≥0) ω +
      Real.exp (-(1 / 100000 : ℝ)) * (2 * y - 4 * y ^ 2) ≤ F := by
    dsimp [F]
    linarith
  exact avram_gbB151_short_gaussian_cash_lower_and_noise_tube_strict_fixedband_excess
    y (D (99 / 100000 : ℝ≥0) ω) F N hYlo hYhi hDivLo hN hF
