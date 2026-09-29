-- Prove2me | solution 1 for FiniteTriangular.sum_range_167
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:20:40.19426+00:00
-- url     : https://prove2.me/submissions/cb657af8-14ab-42dd-a963-aa061b515424

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 167, k = 13861 := by
  rw [sum_range_id]
