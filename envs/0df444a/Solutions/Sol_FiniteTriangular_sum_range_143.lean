-- Prove2me | solution 1 for FiniteTriangular.sum_range_143
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:16:20.492761+00:00
-- url     : https://prove2.me/submissions/70020ffc-9024-4534-8167-38ee3d5cb11d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 143, k = 10153 := by
  rw [sum_range_id]
