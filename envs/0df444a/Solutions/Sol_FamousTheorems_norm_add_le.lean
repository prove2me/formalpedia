-- Prove2me | solution 1 for FamousTheorems.norm_add_le
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-21T21:55:58.869428+00:00
-- url     : https://prove2.me/submissions/ba63c810-4177-4dd2-b82f-ddf8624abbe5

import Mathlib

theorem solution : ∀ {E : Type*} [SeminormedAddGroup E] (a b : E), ‖a + b‖ ≤ ‖a‖ + ‖b‖ :=
  norm_add_le
