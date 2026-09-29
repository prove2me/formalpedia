-- Prove2me | solution 1 for FiniteTriangular.sum_range_886
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:45:20.32729+00:00
-- url     : https://prove2.me/submissions/01228d9c-a2ca-4fbc-801c-02554d5305a5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 886, k = 392055 := by
  rw [sum_range_id]
