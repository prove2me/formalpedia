-- Prove2me | solution 1 for FiniteTriangular.sum_range_532
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:27:30.112188+00:00
-- url     : https://prove2.me/submissions/45219301-5b81-4324-b1be-71d338a30933

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 532, k = 141246 := by
  rw [sum_range_id]
