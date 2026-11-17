-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_compact_band_continuous_second_deriv_abs_bounded
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T17:45:47.340077+00:00
-- url     : https://prove2.me/submissions/a05edb48-4989-49a7-8e74-d05c28d9070a

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology MeasureTheory
open scoped Real
theorem solution
    (w : ℝ → ℝ) (a b : ℝ)
    (hCont : ContinuousOn (fun y => iteratedDeriv 2 w y) (Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y : ℝ, y ∈ Icc a b → |iteratedDeriv 2 w y| ≤ K  := by
  obtain ⟨K, hK⟩ := (isCompact_Icc.exists_bound_of_continuousOn hCont)
  refine ⟨max K 0, le_max_right K 0, ?_⟩
  intro y hy
  have ht := (hK y hy).trans (le_max_left K 0)
  simpa only [Real.norm_eq_abs] using ht
