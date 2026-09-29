-- Prove2me | solution 1 for FiniteTriangular.sum_range_880
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:43:45.238882+00:00
-- url     : https://prove2.me/submissions/ddf7fab0-25ff-4f05-b3e9-5733e936af44

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 880, k = 386760 := by
  rw [sum_range_id]
