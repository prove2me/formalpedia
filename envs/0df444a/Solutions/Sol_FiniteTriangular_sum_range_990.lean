-- Prove2me | solution 1 for FiniteTriangular.sum_range_990
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:37:07.047473+00:00
-- url     : https://prove2.me/submissions/eaf90884-cd35-4886-8840-9346b6633aa7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 990, k = 489555 := by
  rw [sum_range_id]
