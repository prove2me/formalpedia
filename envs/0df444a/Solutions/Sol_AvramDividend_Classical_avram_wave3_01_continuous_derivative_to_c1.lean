-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave3_01_continuous_derivative_to_c1
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-30T21:57:19.467991+00:00
-- url     : https://prove2.me/submissions/474f0118-f68a-464f-9e4c-afd576ee306b

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A continuous derivative candidate determines C¹ regularity on positive
reserves once pointwise derivatives are established. -/
theorem solution
    (f κ : ℝ → ℝ)
    (hκ : ContinuousOn κ (Ioi (0 : ℝ)))
    (hderiv : ∀ a : ℝ, 0 < a → HasDerivAt f (κ a) a) :
    ContDiffOn ℝ 1 f (Ioi (0 : ℝ)) := by
  have hdiff : DifferentiableOn ℝ f (Ioi (0 : ℝ)) := by
    intro a ha
    exact (hderiv a ha).differentiableAt.differentiableWithinAt
  have hcontDeriv : ContinuousOn (deriv f) (Ioi (0 : ℝ)) := by
    apply hκ.congr
    intro a ha
    exact (hderiv a ha).deriv
  have hcontWithin :
      ContinuousOn (derivWithin f (Ioi (0 : ℝ))) (Ioi (0 : ℝ)) := by
    apply hcontDeriv.congr
    intro a ha
    exact derivWithin_of_isOpen isOpen_Ioi ha
  exact (contDiffOn_one_iff_derivWithin isOpen_Ioi.uniqueDiffOn).2
    ⟨hdiff, hcontWithin⟩
