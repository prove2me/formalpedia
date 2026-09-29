-- Prove2me | solution 1 for FiniteTriangular.sum_range_777
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:23:21.748095+00:00
-- url     : https://prove2.me/submissions/8cb6b14b-cb27-4bf2-9819-8b2a23ae6cdb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 777, k = 301476 := by
  rw [sum_range_id]
