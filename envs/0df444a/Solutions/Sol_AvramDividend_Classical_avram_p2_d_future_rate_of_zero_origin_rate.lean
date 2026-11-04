-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_rate_of_zero_origin_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T10:35:53.181196+00:00
-- url     : https://prove2.me/submissions/613b3f4f-1a85-44d6-9092-eefac7b92cae

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original source stationary mean transports any certified origin-window
marked rate to the full physical interval without changing the law or marks. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (hOrigin :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (t - s) ×ˢ B) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by
  simpa only [add_tsub_cancel_of_le hst] using
    (avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
      X s (t - s) B hB).trans hOrigin
