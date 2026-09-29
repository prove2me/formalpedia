-- Prove2me | solution 1 for FiniteTriangular.sum_range_656
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:55:05.844355+00:00
-- url     : https://prove2.me/submissions/bb86362f-7fcc-4a5c-b7c1-70577147556d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 656, k = 214840 := by
  rw [sum_range_id]
