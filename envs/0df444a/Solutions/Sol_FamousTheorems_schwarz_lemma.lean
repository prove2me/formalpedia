-- Prove2me | solution 1 for FamousTheorems.schwarz_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:41:13.242739+00:00
-- url     : https://prove2.me/submissions/c3b34d1b-935f-41ea-8d41-d894f1068b78

import Mathlib

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {R : ℝ} {f : E → F} {z : E} (hd : DifferentiableOn ℂ f (Metric.ball 0 R))
    (h_maps : Set.MapsTo f (Metric.ball 0 R) (Metric.closedBall 0 R)) (h₀ : f 0 = 0) (hz : ‖z‖ < R) :
    ‖f z‖ ≤ ‖z‖ :=
  Complex.norm_le_norm_of_mapsTo_ball hd h_maps h₀ hz
