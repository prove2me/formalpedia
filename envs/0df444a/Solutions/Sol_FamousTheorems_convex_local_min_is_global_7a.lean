-- Prove2me | solution 1 for FamousTheorems.convex_local_min_is_global_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:40:04.298335+00:00
-- url     : https://prove2.me/submissions/60100083-3693-47e5-bae6-2fe57ff5416b

import Mathlib

theorem solution {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] {s : Set E} {f : E → ℝ} {a : E} (ha : a ∈ s)
    (hmin : IsLocalMinOn f s a) (hf : ConvexOn ℝ s f) : IsMinOn f s a :=
  IsMinOn.of_isLocalMinOn_of_convexOn ha hmin hf
