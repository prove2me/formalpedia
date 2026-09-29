-- Prove2me | solution 1 for FiniteTriangular.sum_range_283
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:16:41.781345+00:00
-- url     : https://prove2.me/submissions/00ed8af0-2b41-41cb-8816-0c38d9724ca8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 283, k = 39903 := by
  rw [sum_range_id]
