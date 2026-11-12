-- Prove2me | solution 1 for AvramDividend.Classical.avram_gfinite73_excess_mono_of_deriv
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:45:38.891348+00:00
-- url     : https://prove2.me/submissions/e70227c2-de1d-4dfa-bdaa-d43e0fc61d11

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- A lower derivative bound of one makes the excess value over the
    identity nondecreasing on every compact interior cap interval. -/
theorem solution
    (w : ℝ → ℝ) (a b : ℝ)
    (hcont : ContinuousOn w (Icc a b))
    (hdiff : ∀ z ∈ Ioo a b, DifferentiableAt ℝ w z)
    (hgrad : ∀ z ∈ Ioo a b, 1 ≤ deriv w z) :
    MonotoneOn (fun z : ℝ => w z - z) (Icc a b) := by
  have hd : DifferentiableOn ℝ w
      (interior (Icc a b)) := by
    intro z hz
    have hz' : z ∈ Ioo a b := by simpa [interior_Icc] using hz
    exact (hdiff z hz').differentiableWithinAt
  have hgrad' : ∀ z ∈ interior (Icc a b),
      (1 : ℝ) ≤ deriv w z := by
    intro z hz
    have hz' : z ∈ Ioo a b := by simpa [interior_Icc] using hz
    exact hgrad z hz'
  intro x hx y hy hxy
  have hmul : (1 : ℝ) * (y - x) ≤ w y - w x :=
    (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      hcont hd hgrad' x hx y hy hxy
  dsimp
  linarith
