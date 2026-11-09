-- Prove2me | solution 1 for AvramDividend.Classical.avram_gauss_finitec2_convex_quadratic_upper
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-09T00:45:16.080345+00:00
-- url     : https://prove2.me/submissions/d3cfbc39-c84a-43a9-b2ac-fc0b4718daa8

import Mathlib.Analysis.Convex.Deriv

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open Set
noncomputable section

/-- Convexity of the quadratic correction gives an upper Taylor bound
    simultaneously for ascending and descending Gaussian grid increments. -/
theorem solution
    (w : ℝ → ℝ) (u C L : ℝ)
    (hconvex : ConvexOn ℝ (Icc u C)
      (fun y : ℝ => L / 2 * y ^ 2 - w y))
    (hqderiv : ∀ s ∈ Ico u C,
      HasDerivAt (fun y : ℝ => L / 2 * y ^ 2 - w y)
        (L * s - deriv w s) s) :
    ∀ s ∈ Ico u C, ∀ t ∈ Icc u C,
      w t ≤ w s + deriv w s * (t - s) + L / 2 * (t - s) ^ 2 := by
  intro s hs t ht
  have hs' : s ∈ Icc u C := ⟨hs.1, hs.2.le⟩
  rcases lt_trichotomy s t with hst | heq | hts
  · have hsec := hconvex.le_slope_of_hasDerivAt hs' ht hst (hqderiv s hs)
    rw [slope_def_field] at hsec
    have hdiv := (le_div_iff₀ (sub_pos.mpr hst)).mp hsec
    nlinarith [hdiv]
  · subst t
    simp
  · have hsec := hconvex.slope_le_of_hasDerivAt ht hs' hts (hqderiv s hs)
    rw [slope_def_field] at hsec
    have hdiv := (div_le_iff₀ (sub_pos.mpr hts)).mp hsec
    nlinarith [hdiv]
