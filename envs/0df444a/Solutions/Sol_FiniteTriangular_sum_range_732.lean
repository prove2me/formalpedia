-- Prove2me | solution 1 for FiniteTriangular.sum_range_732
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:12:45.596691+00:00
-- url     : https://prove2.me/submissions/65a2a749-ce4b-4273-9003-38cb7ae10efb

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 732, k = 267546 := by
  rw [sum_range_id]
