-- Prove2me | solution 1 for FiniteTriangular.sum_range_518
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:24:08.004781+00:00
-- url     : https://prove2.me/submissions/53ed1a1d-7680-4272-bd16-806f22c049a5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 518, k = 133903 := by
  rw [sum_range_id]
