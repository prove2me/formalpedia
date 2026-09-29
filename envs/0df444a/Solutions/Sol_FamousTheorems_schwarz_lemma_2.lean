-- Prove2me | solution 2 for FamousTheorems.schwarz_lemma
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:42:09.227336+00:00
-- url     : https://prove2.me/submissions/004fe1e6-6b7b-4656-913b-558cc3509cd7

import Mathlib

theorem solution {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F]
    {R : ℝ} {f : E → F} {z : E} (hd : DifferentiableOn ℂ f (Metric.ball 0 R))
    (h_maps : Set.MapsTo f (Metric.ball 0 R) (Metric.closedBall 0 R)) (h₀ : f 0 = 0) (hz : ‖z‖ < R) :
    ‖f z‖ ≤ ‖z‖ :=
  Complex.norm_le_norm_of_mapsTo_ball hd h_maps h₀ hz
