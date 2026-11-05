-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_future_band_centered_condExp_zero_of_independence
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T07:46:59.542937+00:00
-- url     : https://prove2.me/submissions/2a960d67-7679-4182-8ad6-e865d00a7b97

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical ProbabilityTheory
open scoped NNReal ENNReal

/-- The compensated intrinsic future-band count has zero conditional mean
when its own future-count sigma algebra is independent of the original past. -/
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
    (r : ℝ) (hRate : r =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hJ : Integrable J P)
    (hMean : (∫ ω, J ω ∂P) = r)
    (mFuture : MeasurableSpace Ω) (hFuture : mFuture ≤ mΩ)
    (hStrong : StronglyMeasurable[mFuture] J)
    (hIndependent : Indep mFuture (𝓕 s) P) :
    P[(fun ω => J ω - r) | 𝓕 s] =ᵐ[P] (fun _ => 0) := by
  letI : MeasurableSpace Ω := mΩ
  letI : IsProbabilityMeasure P := X.isProbability
  have hCenterMean : (∫ ω, J ω - r ∂P) = 0 := by
    calc
      _ = (∫ ω, J ω ∂P) - (∫ ω, (r : ℝ) ∂P) := by
        simpa only [Pi.sub_apply] using
          (integral_sub hJ (integrable_const r))
      _ = 0 := by simp [hMean]
  have hStrongCenter :
      StronglyMeasurable[mFuture] (fun ω => J ω - r) :=
    hStrong.sub stronglyMeasurable_const
  have hIndep := condExp_indep_eq hFuture (𝓕.le s)
    hStrongCenter hIndependent
  simpa only [hCenterMean] using hIndep
