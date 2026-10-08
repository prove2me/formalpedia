-- Prove2me | solution 1 for AvramDividend.Classical.secant_of_derivative_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-06T22:54:53.360569+00:00
-- url     : https://prove2.me/submissions/77c1ef22-3e84-4673-8899-f183da92eca1

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- The mean-value inequality with both endpoints included. -/
theorem solution (W : ℝ → ℝ) (c d : ℝ)
    (hcont : ContinuousOn W (Set.Icc 0 c))
    (hdiff : DifferentiableOn ℝ W (Set.Ioo 0 c))
    (hderiv : ∀ t ∈ Set.Ioo 0 c, d ≤ deriv W t) :
    ∀ b x : ℝ, 0 ≤ b → b ≤ x → x ≤ c →
      (x - b) * d ≤ W x - W b := by
  intro b x hb hbx hxc
  have hf : DifferentiableOn ℝ W (interior (Set.Icc 0 c)) := by
    simpa only [interior_Icc] using hdiff
  have hd : ∀ t ∈ interior (Set.Icc 0 c), d ≤ deriv W t := by
    simpa only [interior_Icc] using hderiv
  simpa only [mul_comm] using
    (convex_Icc (0 : ℝ) c).mul_sub_le_image_sub_of_le_deriv hcont hf hd
      b ⟨hb, hbx.trans hxc⟩ x ⟨hb.trans hbx, hxc⟩ hbx
