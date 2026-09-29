-- Prove2me | solution 1 for FiniteTriangular.sum_range_415
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:52:19.848423+00:00
-- url     : https://prove2.me/submissions/64adceaa-ecaf-47a3-953f-d7ed9c737917

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 415, k = 85905 := by
  rw [sum_range_id]
