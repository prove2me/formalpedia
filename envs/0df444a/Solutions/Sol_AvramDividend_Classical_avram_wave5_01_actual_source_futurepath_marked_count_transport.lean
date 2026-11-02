-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_futurepath_marked_count_transport
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:44:56.4477+00:00
-- url     : https://prove2.me/submissions/e1c1f52d-114f-438c-a8f0-8057a14abb4a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_shifted_future_source_leftLim_translation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_count_clock_translation

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The original marked source count is exactly the positive jump-count
functional of its own shifted increment path, on each original sample. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B) :
    ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + T) ×ˢ B) =
    ({v : ℝ≥0 | 0 < v ∧ v ≤ T ∧
      (X.X (s + v) ω - X.X s ω) -
        Function.leftLim
          (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ≠ 0 ∧
      (X.X (s + v) ω - X.X s ω) -
        Function.leftLim
          (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v ∈ B}).encard := by
  have hmark (v : ℝ≥0) (hv : 0 < v) :
      (X.X (s + v) ω - X.X s ω) -
        Function.leftLim
          (fun w : ℝ≥0 => X.X (s + w) ω - X.X s ω) v =
      X.X (s + v) ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) (s + v) := by
    rw [avram_wave5_01_actual_shifted_future_source_leftLim_translation
      X ω s v hv]
    ring
  rw [avram_wave5_01_actual_source_marked_count_clock_translation
    X ω s T B hB]
  apply congrArg (fun S : Set ℝ≥0 => (S.encard : ℝ≥0∞))
  ext v
  by_cases hv : 0 < v
  · simp only [Set.mem_setOf_eq, hv, true_and, hmark v hv]
  · simp only [Set.mem_setOf_eq, hv, false_and]
