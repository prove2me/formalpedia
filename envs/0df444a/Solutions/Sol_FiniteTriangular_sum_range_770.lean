-- Prove2me | solution 1 for FiniteTriangular.sum_range_770
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:21:37.42788+00:00
-- url     : https://prove2.me/submissions/1fbf3c6b-ea69-4463-baa3-0a5c520fc580

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 770, k = 296065 := by
  rw [sum_range_id]
