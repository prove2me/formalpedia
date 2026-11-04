-- Prove2me | solution 1 for AvramDividend.Classical.avram_p2_c_borel_stationary_time_additive
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-03T17:45:23.300318+00:00
-- url     : https://prove2.me/submissions/d7da1090-0f74-480d-938c-5d4c5a9825ec

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Theorems.Thm_AvramDividend_Classical_avram_p2_c_borel_time_rectangle_split

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

/-- Translation-stationary marked rectangle mass is additive over elapsed time. -/
theorem solution
    (μ : Measure (ℝ≥0 × ℝ))
    (B : Set ℝ) (hB : MeasurableSet B)
    (hShift : ∀ (s t : ℝ≥0),
      μ (Ioc s (s + t) ×ˢ B) = μ (Ioc 0 t ×ˢ B))
    (s t : ℝ≥0) :
    μ (Ioc 0 (s + t) ×ˢ B) =
      μ (Ioc 0 s ×ˢ B) + μ (Ioc 0 t ×ˢ B) := by
  calc
    μ (Ioc 0 (s + t) ×ˢ B) =
        μ (Ioc 0 s ×ˢ B) + μ (Ioc s (s + t) ×ˢ B) := by
      exact avram_p2_c_borel_time_rectangle_split μ 0 s (s + t)
        (by simp) (by simp) B hB
    _ = μ (Ioc 0 s ×ˢ B) + μ (Ioc 0 t ×ˢ B) := by
      rw [hShift s t]
