-- Prove2me | solution 1 for FamousTheorems.cauchy_integral_theorem_disk_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:41:06.997981+00:00
-- url     : https://prove2.me/submissions/84235471-8a6a-4f13-a4c5-cecd602bab38

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] {R : ℝ} (h0 : 0 ≤ R) {f : ℂ → E} {c : ℂ}
    {s : Set ℂ} (hs : s.Countable) (hc : ContinuousOn f (Metric.closedBall c R))
    (hd : ∀ z ∈ Metric.ball c R \ s, DifferentiableAt ℂ f z) : (∮ z in C(c, R), f z) = 0 :=
  Complex.circleIntegral_eq_zero_of_differentiable_on_off_countable h0 hs hc hd
