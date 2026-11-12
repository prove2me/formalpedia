-- Prove2me | solution 1 for AvramDividend.Classical.avram_bva21_original_restricted_real_time_ruin_singleton_null
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T21:49:19.205204+00:00
-- url     : https://prove2.me/submissions/c7c0cebb-6f34-43bb-96cd-fa2096cdcc7c

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
noncomputable section

/-- Every individual real time, including the ruin boundary, is null under restricted volume. -/
theorem solution
    (T r : ℝ) :
    ((MeasureTheory.volume : MeasureTheory.Measure ℝ).restrict
      (Set.Icc 0 T)) ({r} : Set ℝ) = 0 := by
  simp
