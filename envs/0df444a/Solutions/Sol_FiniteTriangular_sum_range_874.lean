-- Prove2me | solution 1 for FiniteTriangular.sum_range_874
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:43:41.331627+00:00
-- url     : https://prove2.me/submissions/6cbdae87-7063-4ffa-bcc6-d54d822ffc5f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 874, k = 381501 := by
  rw [sum_range_id]
