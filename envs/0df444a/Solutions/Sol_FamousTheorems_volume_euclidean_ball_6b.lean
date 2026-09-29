-- Prove2me | solution 1 for FamousTheorems.volume_euclidean_ball_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:46:42.18179+00:00
-- url     : https://prove2.me/submissions/35388b84-855a-41f4-ad98-5029971b7ea7

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [FiniteDimensional ℝ E]
    [MeasurableSpace E] [BorelSpace E] [Nontrivial E] (x : E) (r : ℝ) :
    MeasureTheory.volume (Metric.ball x r) =
      ENNReal.ofReal r ^ Module.finrank ℝ E *
        ENNReal.ofReal (Real.sqrt Real.pi ^ Module.finrank ℝ E / Real.Gamma ((Module.finrank ℝ E : ℝ) / 2 + 1)) :=
  InnerProductSpace.volume_ball x r
