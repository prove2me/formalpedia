-- Prove2me | solution 1 for FiniteTriangular.sum_range_269
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:13:00.725225+00:00
-- url     : https://prove2.me/submissions/e63a5a34-9f1e-4051-8b69-ddc29145d8f8

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 269, k = 36046 := by
  rw [sum_range_id]
