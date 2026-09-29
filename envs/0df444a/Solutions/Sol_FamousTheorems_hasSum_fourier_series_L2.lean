-- Prove2me | solution 1 for FamousTheorems.hasSum_fourier_series_L2
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T23:45:36.815572+00:00
-- url     : https://prove2.me/submissions/c9c34452-7a97-41b9-97ca-787bfdf963f0

import Mathlib

open MeasureTheory ProbabilityTheory Filter Set intervalIntegral
open scoped Real Topology ENNReal

theorem solution {T : ℝ} [hT : Fact (0 < T)]
    (f : Lp ℂ 2 (@AddCircle.haarAddCircle T hT)) :
    HasSum (fun i => fourierCoeff (f : AddCircle T → ℂ) i • fourierLp 2 i) f :=
  _root_.hasSum_fourier_series_L2 f
