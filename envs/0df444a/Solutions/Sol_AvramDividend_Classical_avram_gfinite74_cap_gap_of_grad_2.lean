-- Prove2me | solution 2 for AvramDividend.Classical.avram_gfinite74_cap_gap_of_grad
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-11T07:48:22.599849+00:00
-- url     : https://prove2.me/submissions/af2dea47-c005-41e1-a943-e2e57cc9a9f8

import Mathlib

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set

/-- Direct mean-value proof of the finite-cap corner slack. -/
theorem solution
    (w : ℝ → ℝ) (a b : ℝ) (hab : a ≤ b)
    (hcont : ContinuousOn w (Icc a b))
    (hdiff : ∀ z ∈ Ioo a b, DifferentiableAt ℝ w z)
    (hgrad : ∀ z ∈ Ioo a b, 1 ≤ deriv w z) :
    0 ≤ (w b - w a) - (b - a) := by
  have hd : DifferentiableOn ℝ w (interior (Icc a b)) := by
    intro z hz
    have hz' : z ∈ Ioo a b := by simpa [interior_Icc] using hz
    exact (hdiff z hz').differentiableWithinAt
  have hgrad' : ∀ z ∈ interior (Icc a b),
      (1 : ℝ) ≤ deriv w z := by
    intro z hz
    have hz' : z ∈ Ioo a b := by simpa [interior_Icc] using hz
    exact hgrad z hz'
  have ha : a ∈ Icc a b := ⟨le_rfl, hab⟩
  have hb : b ∈ Icc a b := ⟨hab, le_rfl⟩
  have hle : (1 : ℝ) * (b - a) ≤ w b - w a :=
    (convex_Icc a b).mul_sub_le_image_sub_of_le_deriv
      hcont hd hgrad' a ha b hb hab
  linarith
