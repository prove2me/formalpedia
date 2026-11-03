-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_bv_finite_activity_actual_negative_predictable_rectangle
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T19:36:27.719685+00:00
-- url     : https://prove2.me/submissions/b67356ee-3490-4a40-9e44-994799cae3d4

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- A genuine predictable rectangle compensator on the original BV Lévy
source, under the explicitly necessary finite negative-jump activity bound. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hs : 0 < s) (hst : s ≤ t)
    (A : Set Ω) (hA : MeasurableSet[𝓕 s] A) :
    (∫⁻ ω in A,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
      P A * ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by
  have hB : MeasurableSet (Iio (0 : ℝ)) := isOpen_Iio.measurableSet
  obtain ⟨F, hF, hExtract⟩ :=
    avram_wave7_01_original_intrinsic_marked_future_measurable_extractor
      X s t hst (Iio (0 : ℝ)) hB
  have hFactor :=
    avram_wave7_01_intrinsic_future_rectangle_past_factor_of_measurable_extractor
      X s t hst A hA (Iio (0 : ℝ)) hB F hF hExtract
  have hRate :=
    avram_wave6_01_bv_original_future_negative_mark_interval_exact_rate
      X hBV hFinite s t hs hst
  rw [hRate] at hFactor
  simpa only [mul_assoc] using hFactor
