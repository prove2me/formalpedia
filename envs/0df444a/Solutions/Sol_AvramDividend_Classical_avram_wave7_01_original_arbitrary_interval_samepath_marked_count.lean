-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave7_01_original_arbitrary_interval_samepath_marked_count
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-02T12:50:31.462722+00:00
-- url     : https://prove2.me/submissions/28d11168-d6f8-4ade-83aa-07168e2d7289

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

/-! Original marked count on (s,t] is a count of the actual shifted path. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ B) =
    ({v : ℝ≥0 | 0 < v ∧ v ≤ t - s ∧
      (X.X (s + v) ω - X.X s ω) -
        Function.leftLim
          (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ≠ 0 ∧
      (X.X (s + v) ω - X.X s ω) -
        Function.leftLim
          (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ∈ B}).encard := by
  have ht : s + (t - s) = t := by
    simpa only [add_comm] using (tsub_add_cancel_of_le hst)
  simpa only [ht] using
    (avram_wave5_01_actual_source_futurepath_marked_count_transport
      X ω s (t - s) B hB)
