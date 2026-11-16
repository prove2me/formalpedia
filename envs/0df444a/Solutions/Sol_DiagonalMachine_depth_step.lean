-- Prove2me | solution 1 for DiagonalMachine.depth_step
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T18:55:25.197022+00:00
-- url     : https://prove2.me/submissions/3ba6478c-acc4-4f42-9606-775469ef7c97

import Mathlib
open MeasureTheory Set

theorem solution (k u curvature v : ℝ) (hk : 0 < k)
    (hc : 0 ≤ curvature) (hr : v = u-curvature/k^2) : v ≤ u := by
  have h : 0 ≤ curvature/k^2 := div_nonneg hc (sq_nonneg k)
  rw [hr]
  exact sub_le_self _ h
