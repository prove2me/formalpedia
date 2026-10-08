-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_Ioi_of_differentiableAt_continuous_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T17:42:55.107356+00:00
-- url     : https://prove2.me/submissions/0e59b94a-3786-4151-89fe-c4ec8aa38172

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (W : ℝ → ℝ)
    (hdiff : ∀ x : ℝ, 0 < x → DifferentiableAt ℝ W x)
    (hcont : ContinuousOn (deriv W) (Ioi 0)) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioi (0 : ℝ))]
  constructor
  · intro x hx
    have hxpos : 0 < x := by
      simpa only [Set.mem_Ioi] using hx
    exact (hdiff x hxpos).differentiableWithinAt
  · exact hcont.congr (by
      intro x hx
      exact derivWithin_of_isOpen isOpen_Ioi hx)
