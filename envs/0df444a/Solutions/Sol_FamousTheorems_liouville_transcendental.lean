-- Prove2me | solution 1 for FamousTheorems.liouville_transcendental
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:58.888672+00:00
-- url     : https://prove2.me/submissions/1c0f3cef-48e0-4e94-9919-50a21ecad253

import Mathlib

theorem solution : ∀ {x : ℝ}, Liouville x → Transcendental ℤ x :=
  Liouville.transcendental
