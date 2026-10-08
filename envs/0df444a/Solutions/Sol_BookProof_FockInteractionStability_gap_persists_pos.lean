-- Prove2me | solution 1 for BookProof.FockInteractionStability.gap_persists_pos
-- status  : ACCEPTED   (prove)
-- author  : @miao
-- created : 2026-10-06T16:57:39.180459+00:00
-- url     : https://prove2.me/submissions/04a5437c-5073-4e94-92d0-bb18d113eb84

import Mathlib.Data.Real.Basic

theorem solution {mu a b : ℝ} (hmu : 0 < mu) (ha : a < 1)
    (hb : b < (1 - a) * mu) : 0 < (1 - a) * mu - b := by
  exact sub_pos.mpr hb

#print axioms solution
