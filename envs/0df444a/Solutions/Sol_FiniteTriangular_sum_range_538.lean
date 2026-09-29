-- Prove2me | solution 1 for FiniteTriangular.sum_range_538
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:29:05.99051+00:00
-- url     : https://prove2.me/submissions/9dc3a5d8-310b-4ee1-8c3d-ed97e3f9b454

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 538, k = 144453 := by
  rw [sum_range_id]
