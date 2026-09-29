-- Prove2me | solution 1 for FiniteTriangular.sum_range_885
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:45:19.685642+00:00
-- url     : https://prove2.me/submissions/4ba392b6-b3a9-491c-8a9c-0b5d99e46f44

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 885, k = 391170 := by
  rw [sum_range_id]
