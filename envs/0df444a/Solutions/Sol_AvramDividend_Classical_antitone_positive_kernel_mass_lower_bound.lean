-- Prove2me | solution 1 for AvramDividend.Classical.antitone_positive_kernel_mass_lower_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-23T11:20:33.788397+00:00
-- url     : https://prove2.me/submissions/1efdf46b-dc50-4eb5-a8e9-a629d0367a42

import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.Order.Monotone.Defs

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set

/-- An antitone kernel is at most its positive-horizon average. -/
theorem solution
    (K : ℝ → ℝ) (hanti : AntitoneOn K (Ioi (0 : ℝ)))
    (x : ℝ) (hx : 0 < x)
    (hint : IntervalIntegrable K volume 0 x) :
    x * K x ≤ ∫ t in (0 : ℝ)..x, K t := by
  have hpoint : ∀ t ∈ Ioo (0 : ℝ) x, K x ≤ K t := by
    intro t ht
    exact hanti ht.1 hx ht.2.le
  have hbound :
      (∫ t in (0 : ℝ)..x, K x) ≤ ∫ t in (0 : ℝ)..x, K t :=
    intervalIntegral.integral_mono_on_of_le_Ioo hx.le intervalIntegrable_const hint hpoint
  simpa [intervalIntegral.integral_const, smul_eq_mul] using hbound
