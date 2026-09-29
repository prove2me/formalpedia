-- Prove2me | solution 1 for FiniteTriangular.sum_range_678
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:00:14.299261+00:00
-- url     : https://prove2.me/submissions/32b2a535-af78-4989-8ec8-53161c6a358e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 678, k = 229503 := by
  rw [sum_range_id]
