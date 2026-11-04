-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_all_countable_finite_band_counts_ae_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T23:32:25.902033+00:00
-- url     : https://prove2.me/submissions/e61574da-7169-424f-bfd3-b9b63147a114

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Under finite original Lévy intensities and physical marked-count rates,
almost every original path has finite counts at every countable cutoff. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : ℕ → Set ℝ)
    (J : ℕ → Ω → ℝ≥0∞)
    (hJsource : ∀ n ω, J n ω =
      ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B n))
    (hMeas : ∀ n, Measurable (J n))
    (hRate : ∀ n, (∫⁻ ω, J n ω ∂P) =
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (B n)))
    (hFinite : ∀ n, X.ν (B n) ≠ ⊤) :
    ∀ᵐ ω ∂P, ∀ n, J n ω < ⊤ := by
  have hEach (n : ℕ) : ∀ᵐ ω ∂P, J n ω < ⊤ := by
    exact (avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite
      X s t (B n) (J n) (hJsource n)
      (hMeas n) (hRate n) (hFinite n)).2
  exact ae_all_iff.mpr hEach
