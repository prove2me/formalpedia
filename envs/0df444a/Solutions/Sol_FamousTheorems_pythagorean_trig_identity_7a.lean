-- Prove2me | solution 1 for FamousTheorems.pythagorean_trig_identity_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T12:25:41.813371+00:00
-- url     : https://prove2.me/submissions/fb24eba4-d909-473b-9d74-cf5d36adbc11

import Mathlib

theorem solution (x : ℝ) : Real.sin x ^ 2 + Real.cos x ^ 2 = 1 :=
  Real.sin_sq_add_cos_sq x
