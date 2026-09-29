-- Prove2me | solution 1 for FiniteTriangular.sum_range_893
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:47:08.716198+00:00
-- url     : https://prove2.me/submissions/10c41e94-febb-44e1-84d8-040320a5b5dc

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 893, k = 398278 := by
  rw [sum_range_id]
