-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_compensated_variance_of_factorial_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:30:46.616261+00:00
-- url     : https://prove2.me/submissions/a2c198ed-0425-4181-9fc7-4ae7ea2eafd9

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_raw_second_of_factorial_moment
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_compensated_variance_of_raw_moments

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- A genuine original marked-count factorial-moment identity yields the
diagonal compensated quadratic moment for its own physical source P. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J : Ω → ℝ)
    (hSource : ∀ ω, J ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hJ : Integrable J P)
    (hFactorialIntegrable : Integrable (fun ω => J ω * (J ω - 1)) P)
    (r : ℝ) (hRate : r =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hFirst : (∫ ω, J ω ∂P) = r)
    (hFactorial : (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2) :
    (∫ ω, (J ω - r) ^ 2 ∂P) = r := by
  have hJ2 : Integrable (fun ω : Ω => (J ω) ^ 2) P := by
    have hIdent : (fun ω : Ω => (J ω) ^ 2) =
        (fun ω : Ω => J ω * (J ω - 1)) + J := by
      funext ω
      simp only [Pi.add_apply]
      ring
    rw [hIdent]
    exact hFactorialIntegrable.add hJ
  have hSecond : (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + r :=
    avram_p4_b_smalljump_original_finite_band_raw_second_of_factorial_moment
      X s t B J hSource hJ hFactorialIntegrable r hRate hFirst hFactorial
  exact avram_p4_b_smalljump_original_finite_band_compensated_variance_of_raw_moments
    X s t B J hSource hJ hJ2 r hRate hFirst hSecond
