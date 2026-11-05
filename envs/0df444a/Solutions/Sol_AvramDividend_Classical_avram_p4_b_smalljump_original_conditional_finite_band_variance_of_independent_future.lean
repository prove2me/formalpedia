-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_conditional_finite_band_variance_of_independent_future
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:33:07.448982+00:00
-- url     : https://prove2.me/submissions/ea3ef18e-353a-4115-90d8-8abd277b7a28

import Mathlib.Probability.ConditionalExpectation
import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_band_compensated_variance_of_factorial_moment

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal

/-- An independent original future-count sigma-algebra and the physical
factorial moment identify the original conditional diagonal variance. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
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
    (hFactorial : (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2)
    (mFuture : MeasurableSpace Ω) (hFuture : mFuture ≤ mΩ)
    (hSqMeas : StronglyMeasurable[mFuture] (fun ω => (J ω - r) ^ 2))
    (hFutureIndependent : Indep mFuture (𝓕 s) P) :
    P[(fun ω => (J ω - r) ^ 2) | 𝓕 s] =ᵐ[P] (fun _ => r) := by
  -- Keep the ambient source measurable space ahead of the future subspace
  -- when elaborating the conditional-expectation independence lemma.
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := X.isProbability
  have hVariance : (∫ ω, (J ω - r) ^ 2 ∂P) = r :=
    avram_p4_b_smalljump_original_finite_band_compensated_variance_of_factorial_moment
      X s t B J hSource hJ hFactorialIntegrable r hRate hFirst hFactorial
  have hIndep := condExp_indep_eq hFuture (𝓕.le s)
    hSqMeas hFutureIndependent
  simpa only [hVariance] using hIndep
