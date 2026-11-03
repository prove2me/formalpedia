-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_bv_negative_mark_past_rectangle_of_measurable_extractor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:09:31.537576+00:00
-- url     : https://prove2.me/submissions/6b836393-b1e2-4c1c-8861-c2e3b3a0cb75

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The actual finite-activity BV negative-mark rate factors from the
original past once its count is extracted measurably from future increments. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A)
    (F : (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : Measurable F)
    (hExtract : ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) =
      F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
    P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  have hFactor :=
    avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
      X s t hst A hA (Iio (0 : ℝ)) measurableSet_Iio F hF hExtract
  have hRate :=
    avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
      X hBV hFinite s t hs hst
  calc
    _ = P A * (∫⁻ ω,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) := hFactor
    _ = P A * ((t - s : ℝ≥0) : ℝ≥0∞) *
        X.ν (Iio (0 : ℝ)) := by rw [hRate, mul_assoc]
