-- Prove2me | solution 1 for AvramDividend.Classical.contDiffOn_one_of_differentiable_continuous_deriv_Ioi
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-07T21:05:19.53399+00:00
-- url     : https://prove2.me/submissions/83615a5a-c355-4f25-9620-c6c77f739909

import Mathlib


set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

theorem solution
    (W : ℝ → ℝ)
    (hdiff : DifferentiableOn ℝ W (Ioi 0))
    (hcont : ContinuousOn (deriv W) (Ioi 0)) :
    ContDiffOn ℝ 1 W (Ioi 0) := by
  rw [contDiffOn_one_iff_derivWithin (uniqueDiffOn_Ioi (0 : ℝ))]
  refine ⟨hdiff, ?_⟩
  apply hcont.congr
  intro x hx
  exact derivWithin_of_isOpen isOpen_Ioi hx
