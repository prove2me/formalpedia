-- Prove2me | solution 1 for AvramDividend.Classical.avram_wave5_04c_C1_extended_difference_quotient_continuous
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-01T18:10:44.20608+00:00
-- url     : https://prove2.me/submissions/a5c8d9e3-453c-494d-ab32-b9333665d91f

import Mathlib
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

set_option autoImplicit false
open Filter Set

/-! Extend a derivative difference quotient continuously across its base point. -/
theorem solution (f : ℝ → ℝ) (c a : ℝ)
    (hf : HasDerivAt f a c) (s : Set ℝ)
    (hfc : ∀ t ∈ s, t ≠ c → ContinuousAt f t) :
    ContinuousOn
      (Function.update (fun t : ℝ => (f t - f c) / (t - c)) c a) s := by
  intro t ht
  by_cases htc : t = c
  · subst t
    exact hf.continuousAt_div.continuousWithinAt
  · apply ContinuousAt.continuousWithinAt
    rw [continuousAt_update_of_ne htc]
    exact ((hfc t ht htc).sub continuousAt_const).div
      (continuousAt_id.sub continuousAt_const) (sub_ne_zero.mpr htc)
