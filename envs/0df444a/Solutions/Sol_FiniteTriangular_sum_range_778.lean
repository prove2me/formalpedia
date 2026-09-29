-- Prove2me | solution 1 for FiniteTriangular.sum_range_778
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:23:22.398361+00:00
-- url     : https://prove2.me/submissions/c6959dde-6c48-4484-beb0-51e14b103baa

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 778, k = 302253 := by
  rw [sum_range_id]
