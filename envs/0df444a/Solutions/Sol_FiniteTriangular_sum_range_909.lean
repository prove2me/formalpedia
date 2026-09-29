-- Prove2me | solution 1 for FiniteTriangular.sum_range_909
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:50:23.41529+00:00
-- url     : https://prove2.me/submissions/355fe6a0-202d-47fe-b0a4-eb336a12ce58

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 909, k = 412686 := by
  rw [sum_range_id]
