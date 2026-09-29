-- Prove2me | solution 1 for FamousTheorems.exists_deriv_eq_slope
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T22:10:48.146044+00:00
-- url     : https://prove2.me/submissions/5bc7e63a-190e-4dc8-bc29-3ee35bb51a1b

import Mathlib

theorem solution : ∀ (f : ℝ → ℝ) {a b : ℝ}, a < b →
    ContinuousOn f (Set.Icc a b) → DifferentiableOn ℝ f (Set.Ioo a b) →
    ∃ c ∈ Set.Ioo a b, deriv f c = (f b - f a) / (b - a) :=
  exists_deriv_eq_slope
