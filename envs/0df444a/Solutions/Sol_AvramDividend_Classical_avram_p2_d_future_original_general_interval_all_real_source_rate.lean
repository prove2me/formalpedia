-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_d_future_original_general_interval_all_real_source_rate
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T20:43:53.937352+00:00
-- url     : https://prove2.me/submissions/8e524d25-fbfd-4078-b46d-6bc589d2f2d7

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
import Theorems.Thm_AvramDividend_Classical_avram_p2_d_future_original_zero_origin_all_real_source_rate

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original marked count on any real source interval has the single
unit-time source count-derived rate; ν identification remains separate. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (1 : ℝ≥0) ×ˢ B) ∂P) := by
  have hsum : s + (t - s) = t := by
    simpa only [add_comm] using (tsub_add_cancel_of_le hst)
  have hShift :=
    avram_wave7_01_original_intrinsic_marked_rectangle_count_stationary_mean
      X s (t - s) B hB
  rw [hsum] at hShift
  exact hShift.trans
    (avram_p2_d_future_original_zero_origin_all_real_source_rate X B hB (t - s))
