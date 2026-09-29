-- Prove2me | solution 1 for FiniteTriangular.sum_range_491
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:18:58.157118+00:00
-- url     : https://prove2.me/submissions/96f4a138-987b-42f6-8610-db864997907e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 491, k = 120295 := by
  rw [sum_range_id]
