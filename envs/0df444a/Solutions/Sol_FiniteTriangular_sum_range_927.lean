-- Prove2me | solution 1 for FiniteTriangular.sum_range_927
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:53:48.618919+00:00
-- url     : https://prove2.me/submissions/a43aeaed-6bec-423d-8008-46ad24c2b200

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 927, k = 429201 := by
  rw [sum_range_id]
