-- Prove2me | solution 1 for FiniteTriangular.sum_range_422
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:54:05.388878+00:00
-- url     : https://prove2.me/submissions/001f4092-37e5-45e6-ba18-2568d7c5a013

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 422, k = 88831 := by
  rw [sum_range_id]
