-- Prove2me | solution 1 for FamousTheorems.convex_continuous_on_interior_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:38:01.715617+00:00
-- url     : https://prove2.me/submissions/40314dea-4b0e-4850-b1bf-1e8a7ee8d1f1

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E] {C : Set E} {f : E → ℝ}
    (hf : ConvexOn ℝ C f) : ContinuousOn f (interior C) :=
  hf.continuousOn_interior
