-- Prove2me | solution 1 for FiniteTriangular.sum_range_395
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:48:53.656638+00:00
-- url     : https://prove2.me/submissions/c94ff5fb-7ef8-4084-bf19-3b16f1a464d1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 395, k = 77815 := by
  rw [sum_range_id]
