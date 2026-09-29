-- Prove2me | solution 1 for FiniteTriangular.sum_range_258
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:11:13.526643+00:00
-- url     : https://prove2.me/submissions/f2e5bd3d-3b08-4c41-ad3c-134ac5151d32

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 258, k = 33153 := by
  rw [sum_range_id]
