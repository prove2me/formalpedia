-- Prove2me | solution 1 for FiniteTriangular.sum_range_209
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:51:41.409276+00:00
-- url     : https://prove2.me/submissions/e3cc177c-75fe-46df-b8de-3a59ee6c09b8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 209, k = 21736 := by
  rw [sum_range_id]
