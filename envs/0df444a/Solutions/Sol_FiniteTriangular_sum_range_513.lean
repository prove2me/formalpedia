-- Prove2me | solution 1 for FiniteTriangular.sum_range_513
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:24:04.885773+00:00
-- url     : https://prove2.me/submissions/b2ed86d9-803b-45ce-a7a9-5bb0adbc4b93

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 513, k = 131328 := by
  rw [sum_range_id]
