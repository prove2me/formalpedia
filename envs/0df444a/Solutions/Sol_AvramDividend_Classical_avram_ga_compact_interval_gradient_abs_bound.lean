-- Prove2me | solution 1 for AvramDividend.Classical.avram_ga_compact_interval_gradient_abs_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-16T18:02:19.3371+00:00
-- url     : https://prove2.me/submissions/d1f27820-f4e5-40a9-8770-0a5eee998f35

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set Filter Topology MeasureTheory
theorem solution
    (w : ℝ → ℝ) (a b : ℝ)
    (hCont : ContinuousOn (deriv w) (Icc a b)) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ y : ℝ,
      y ∈ Icc a b → |deriv w y| ≤ K  := by
  obtain ⟨K, hK⟩ := (isCompact_Icc.exists_bound_of_continuousOn hCont)
  refine ⟨max K 0, le_max_right K 0, ?_⟩
  intro y hy
  have ht := (hK y hy).trans (le_max_left K 0)
  simpa only [Real.norm_eq_abs] using ht
