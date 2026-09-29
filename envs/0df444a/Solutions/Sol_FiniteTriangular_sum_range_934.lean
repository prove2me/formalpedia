-- Prove2me | solution 1 for FiniteTriangular.sum_range_934
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:55:35.053263+00:00
-- url     : https://prove2.me/submissions/9507c42e-3fcc-49f5-859c-f185b4df5b3e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 934, k = 435711 := by
  rw [sum_range_id]
