-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_01_actual_source_relative_stopped_band_count_identification_finite
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T14:49:23.342138+00:00
-- url     : https://prove2.me/submissions/b9783e4c-9976-4475-8b28-a5e1f0280582

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_marked_count_clock_translation
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_random_clock_clipped_separated_jump_count_finite
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

/-- The marked jump count in a relative stopped time window is exactly the
finite cardinality of the original path's source jumps. -/
theorem solution
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (s T : ℝ≥0) (τ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ) :
    (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + min (τ ω) T) ×ˢ {y : ℝ | δ ≤ dist y 0}) = ({v : ℝ≥0 | 0 < v ∧ v ≤ min (τ ω) T ∧
      X.X (s + v) ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) (s + v) ≠ 0 ∧
      δ ≤ dist (X.X (s + v) ω -
        Function.leftLim (fun w : ℝ≥0 => X.X w ω) (s + v)) 0}).encard) ∧
      (((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s (s + min (τ ω) T) ×ˢ {y : ℝ | δ ≤ dist y 0}) < ⊤) := by
  have hB : MeasurableSet {y : ℝ | δ ≤ dist y 0} := by
    exact (isClosed_le continuous_const
      (continuous_id.dist continuous_const)).measurableSet
  constructor
  · simpa only [Set.mem_setOf_eq] using
      (avram_wave5_01_actual_source_marked_count_clock_translation
        X ω s (min (τ ω) T) {y : ℝ | δ ≤ dist y 0} hB)
  · have hfinite :=
      avram_wave5_01_actual_source_random_clock_clipped_separated_jump_count_finite
        X ω s (s + min (τ ω) T)
        (fun _ => s + min (τ ω) T) δ hδ
    simpa only [min_self] using hfinite
