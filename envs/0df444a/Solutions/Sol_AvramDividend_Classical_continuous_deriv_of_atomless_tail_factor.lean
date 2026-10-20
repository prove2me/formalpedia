-- Prove2me | solution 1 for AvramDividend.Classical.continuous_deriv_of_atomless_tail_factor
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-19T20:44:22.717946+00:00
-- url     : https://prove2.me/submissions/5c47e725-5d7f-4448-acca-1dc028d379b5

import Mathlib
import Theorems.Thm_AvramDividend_Classical_continuous_deriv_of_const_add_atomless_pos_tail_factor

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- Continuity of an atomless finite-tail derivative factor follows from
    the already proved constant-plus-tail criterion with zero constant. -/
theorem solution
    (μ : Measure ℝ) [NullSingletonClass μ]
    (hfin : ∀ x : ℝ, μ (Ici x) ≠ ⊤)
    (W : ℝ → ℝ)
    (hWcont : ContinuousOn W (Ioi 0))
    (hderiv : ∀ x : ℝ, 0 < x → deriv W x = W x * μ.real (Ici x)) :
    ContinuousOn (deriv W) (Ioi 0) := by
  exact AvramDividend.Classical.continuous_deriv_of_const_add_atomless_pos_tail_factor
    μ (fun x _ => hfin x) 0 W hWcont
    (by
      intro x hx
      simpa only [zero_add] using hderiv x hx)
