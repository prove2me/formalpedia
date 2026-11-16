-- Prove2me | solution 1 for FixedKMachine.stationary_identity
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:56:00.751199+00:00
-- url     : https://prove2.me/submissions/ea5d58c0-6c2b-4cd0-a635-21ab51ccb05e

import Mathlib
open MeasureTheory Set

theorem solution (n u derivative v : ℝ)
    (hr : v = u-derivative/n) (hd : derivative = 0) : v = u := by
  simpa [hd] using hr
