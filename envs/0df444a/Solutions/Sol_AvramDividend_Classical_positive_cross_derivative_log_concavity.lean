-- Prove2me | solution 1 for AvramDividend.Classical.positive_cross_derivative_log_concavity
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-25T13:48:38.608395+00:00
-- url     : https://prove2.me/submissions/ac69ae7a-05a5-4e84-a6cf-79b905717d62

import Theorems.Thm_AvramDividend_Classical_concave_log_of_antitone_log_derivative
import Mathlib.Algebra.Order.Field.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open AvramDividend.Classical Set

/-- Positive cross-derivative order forces log-concavity without second derivatives. -/
theorem solution
    (f : ℝ → ℝ)
    (hpos : ∀ x : ℝ, 0 < x → 0 < f x)
    (hdiff : ∀ x : ℝ, 0 < x → HasDerivAt f (deriv f x) x)
    (hcross : ∀ x y : ℝ, 0 < x → x ≤ y →
      deriv f y * f x ≤ deriv f x * f y) :
    ConcaveOn ℝ (Ioi (0 : ℝ)) (fun z : ℝ => Real.log (f z)) := by
  apply concave_log_of_antitone_log_derivative f hpos hdiff
  intro x hx y hy hxy
  exact (div_le_div_iff₀ (hpos y hy) (hpos x hx)).2
    (hcross x y hx hxy)
