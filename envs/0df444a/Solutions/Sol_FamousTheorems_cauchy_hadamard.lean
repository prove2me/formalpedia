-- Prove2me | solution 1 for FamousTheorems.cauchy_hadamard
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T17:48:45.618437+00:00
-- url     : https://prove2.me/submissions/e580cd81-f1ec-4dae-9458-9a6fcd99f077

import Mathlib

theorem solution {𝕜 : Type*} [NontriviallyNormedField 𝕜] {E F : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E]
    [NormedAddCommGroup F] [NormedSpace 𝕜 F] (p : FormalMultilinearSeries 𝕜 E F) :
    p.radius⁻¹ = Filter.limsup (fun n : ℕ => ((‖p n‖₊ ^ (1 / (n : ℝ)) : NNReal) : ENNReal)) Filter.atTop :=
  p.radius_inv_eq_limsup
