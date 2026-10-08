-- Prove2me | solution 1 for AvramDividend.Classical.continuousOn_Ici_of_continuousOn_Icc_zero
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-08T06:24:12.139575+00:00
-- url     : https://prove2.me/submissions/4270b80c-5134-4ffb-8e44-f0c5bbdf8e9d

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true
open Set

/-- Continuity on all finite initial intervals extends to the nonnegative ray. -/
theorem solution
    (f : ℝ → ℝ)
    (hcompact : ∀ B : ℝ, 0 ≤ B → ContinuousOn f (Icc (0 : ℝ) B)) :
    ContinuousOn f (Ici (0 : ℝ)) := by
  apply continuousOn_of_locally_continuousOn
  intro x hx
  refine ⟨Iio (x + 1), isOpen_Iio, ?_, ?_⟩
  · change x < x + 1
    linarith
  · have hx0 : 0 ≤ x := hx
    have hB : 0 ≤ x + 1 := by linarith
    exact (hcompact (x + 1) hB).mono (by
      intro y hy
      exact ⟨hy.1, hy.2.le⟩)
