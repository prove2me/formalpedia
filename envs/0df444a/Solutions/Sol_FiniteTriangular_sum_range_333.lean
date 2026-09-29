-- Prove2me | solution 1 for FiniteTriangular.sum_range_333
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:34:19.424517+00:00
-- url     : https://prove2.me/submissions/49fe8bd6-f0fe-48f3-8ad9-b2297293127d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 333, k = 55278 := by
  rw [sum_range_id]
