-- Prove2me | solution 1 for FiniteTriangular.sum_range_782
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:23:24.893024+00:00
-- url     : https://prove2.me/submissions/d698183d-e2bc-40e8-93bd-52b1bd1df658

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 782, k = 305371 := by
  rw [sum_range_id]
