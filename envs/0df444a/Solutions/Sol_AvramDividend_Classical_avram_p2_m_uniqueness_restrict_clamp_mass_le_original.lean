-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_m_uniqueness_restrict_clamp_mass_le_original
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T16:53:48.308425+00:00
-- url     : https://prove2.me/submissions/f6050e53-d7ea-41e8-9638-8c5d07c00feb

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

/-- The restricted, clamped original law has no more total mass than the
original law. This transfers P2-B's original X.X mass estimate exactly. -/
theorem solution (μ : Measure ℝ) :
    ((μ.restrict (Set.Iio (1 : ℝ))).map
      (fun z : ℝ => max (0 : ℝ) (min 1 z))) Set.univ ≤ μ Set.univ := by
  have hm : Measurable (fun z : ℝ => max (0 : ℝ) (min 1 z)) :=
    measurable_const.max (measurable_const.min measurable_id)
  calc
    ((μ.restrict (Set.Iio (1 : ℝ))).map
        (fun z : ℝ => max (0 : ℝ) (min 1 z))) Set.univ =
        μ (Set.Iio (1 : ℝ)) := by
      rw [Measure.map_apply hm MeasurableSet.univ]
      simp
    _ ≤ μ Set.univ := measure_mono (Set.subset_univ _)
