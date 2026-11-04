-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_raw_second_of_factorial_moment
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:06:17.362767+00:00
-- url     : https://prove2.me/submissions/5283ed7c-be9c-4f22-af93-b11c12fb1e7d

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The first and second factorial moments of the actual original
intrinsic marked count determine its raw second moment under physical P. -/
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
    (hFactorial : (∫ ω, J ω * (J ω - 1) ∂P) = r ^ 2) :
    (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + r := by
  have hId (ω : Ω) :
      (J ω) ^ 2 = J ω * (J ω - 1) + J ω := by
    ring
  simp_rw [hId]
  rw [integral_add hFactorialIntegrable hJ, hFactorial, hFirst]
