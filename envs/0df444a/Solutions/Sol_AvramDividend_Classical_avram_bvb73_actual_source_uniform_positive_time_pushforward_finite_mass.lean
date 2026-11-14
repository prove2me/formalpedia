-- Prove2me | solution 1 for AvramDividend.Classical.avram_bvb73_actual_source_uniform_positive_time_pushforward_finite_mass
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-13T23:06:02.382213+00:00
-- url     : https://prove2.me/submissions/80ce0cfa-4f84-4d86-9a43-106c11027594

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal
noncomputable section

theorem solution
    (T : ℝ) (hT : 0 < T) :
    ((((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
      Set.univ) < ⊤ := by
  have hMass :
      ((((volume : Measure ℝ).restrict (Icc 0 T)).map Real.toNNReal)
        Set.univ) = ENNReal.ofReal T := by
    rw [Measure.map_apply measurable_real_toNNReal (by measurability)]
    simp [Real.volume_Icc]
  rw [hMass]
  exact ENNReal.ofReal_lt_top
