-- Prove2me | solution 1 for FiniteTriangular.sum_range_441
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:08:13.01438+00:00
-- url     : https://prove2.me/submissions/3ba7b01f-a5cd-4c38-bf92-49b184c9262c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 441, k = 97020 := by
  rw [sum_range_id]
