-- Prove2me | solution 1 for AvramDividend.Classical.avram_p4_b_smalljump_original_finite_band_compensated_variance_of_raw_moments
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T00:23:16.301149+00:00
-- url     : https://prove2.me/submissions/b5473520-54d2-42d2-8903-a6e791644f0b

import Mathlib.Probability.Process.Filtration
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- The first two raw moments of the actual original marked-jump count
give its compensated L2 variance, retaining the physical probability law. -/
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
    (hJ2 : Integrable (fun ω => (J ω) ^ 2) P)
    (r : ℝ) (hRate : r =
      ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hFirst : (∫ ω, J ω ∂P) = r)
    (hSecond : (∫ ω, (J ω) ^ 2 ∂P) = r ^ 2 + r) :
    (∫ ω, (J ω - r) ^ 2 ∂P) = r := by
  have hLinear : Integrable (fun ω => 2 * r * J ω) P :=
    hJ.const_mul _
  have hConst : Integrable (fun _ : Ω => r ^ 2) P :=
    integrable_const _
  have hAdd :
      (∫ ω, (J ω) ^ 2 - 2 * r * J ω + r ^ 2 ∂P) =
      (∫ ω, (J ω) ^ 2 - 2 * r * J ω ∂P) +
        (∫ _ : Ω, r ^ 2 ∂P) := by
    simpa only [Pi.add_apply, Pi.sub_apply] using
      (integral_add (hJ2.sub hLinear) hConst)
  have hSub :
      (∫ ω, (J ω) ^ 2 - 2 * r * J ω ∂P) =
      (∫ ω, (J ω) ^ 2 ∂P) - (∫ ω, 2 * r * J ω ∂P) := by
    simpa only [Pi.sub_apply] using (integral_sub hJ2 hLinear)
  calc
    _ = (∫ ω, (J ω) ^ 2 - 2 * r * J ω + r ^ 2 ∂P) := by
      apply integral_congr_ae
      filter_upwards [] with ω
      ring
    _ = (∫ ω, (J ω) ^ 2 - 2 * r * J ω ∂P) +
        (∫ _ : Ω, r ^ 2 ∂P) := hAdd
    _ = ((∫ ω, (J ω) ^ 2 ∂P) -
        (∫ ω, 2 * r * J ω ∂P)) + r ^ 2 := by
      rw [hSub]
      simp
    _ = r := by
      rw [integral_const_mul, hFirst, hSecond]
      ring
