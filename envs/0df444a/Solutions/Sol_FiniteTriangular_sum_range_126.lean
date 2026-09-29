-- Prove2me | solution 1 for FiniteTriangular.sum_range_126
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:13:23.460301+00:00
-- url     : https://prove2.me/submissions/13f2b4b9-4835-40b2-b702-55316a1f0906

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 126, k = 7875 := by
  rw [sum_range_id]
