-- Prove2me | solution 1 for FiniteTriangular.sum_range_837
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:35:21.972279+00:00
-- url     : https://prove2.me/submissions/63c6da8c-86d0-4412-b269-8e7bb911a113

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 837, k = 349866 := by
  rw [sum_range_id]
