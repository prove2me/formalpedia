-- Prove2me | solution 1 for AvramDividend.Classical.avram_p3_e_compensator_local_Lipschitz_of_derivative_bound
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-11-04T13:12:46.959365+00:00
-- url     : https://prove2.me/submissions/432e2f2b-ddf4-4734-b6b4-2f5c88b13765

import Mathlib
open Set
noncomputable section
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

theorem solution
(w : ℝ → ℝ) (a b L : ℝ)
(hdiff : ∀ y ∈ Set.Icc (a / 2) b, DifferentiableAt ℝ w y)
(hderiv : ∀ y ∈ Set.Icc (a / 2) b, |deriv w y| ≤ L) :
∀ u ∈ Set.Icc (a / 2) b, ∀ v ∈ Set.Icc (a / 2) b,
  |w u - w v| ≤ L * |u - v| := by
  intro u hu v hv
  have hbound : ∀ y ∈ Icc (a / 2) b, ‖deriv w y‖ ≤ L := by
    intro y hy
    simpa [Real.norm_eq_abs] using hderiv y hy
  have hconv : Convex ℝ (Icc (a / 2) b) := convex_Icc (a / 2) b
  have h := hconv.norm_image_sub_le_of_norm_deriv_le hdiff hbound hv hu
  simpa [Real.norm_eq_abs] using h
