-- Prove2me | solution 1 for FiniteTriangular.sum_range_1045
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:13:19.403919+00:00
-- url     : https://prove2.me/submissions/c68e4be2-76eb-43e7-bc94-357949ea429f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1045, k = 545490 := by
  rw [sum_range_id]
