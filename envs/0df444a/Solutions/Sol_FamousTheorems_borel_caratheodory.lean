-- Prove2me | solution 1 for FamousTheorems.borel_caratheodory
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T18:16:39.048274+00:00
-- url     : https://prove2.me/submissions/df51b13a-13a6-4f91-b3d9-5690347822a2

import Mathlib

theorem solution {f : ℂ → ℂ} {M R : ℝ} {z : ℂ} (hM : 0 < M) (hf : DifferentiableOn ℂ f (Metric.ball 0 R))
    (hfM : Set.MapsTo f (Metric.ball 0 R) {w : ℂ | w.re ≤ M}) (hR : 0 < R) (hz : z ∈ Metric.ball 0 R) :
    ‖f z‖ ≤ 2 * M * ‖z‖ / (R - ‖z‖) + ‖f 0‖ * (R + ‖z‖) / (R - ‖z‖) :=
  Complex.borelCaratheodory hM hf hfM hR hz
