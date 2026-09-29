-- Prove2me | solution 1 for FiniteTriangular.sum_range_306
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:22:04.997739+00:00
-- url     : https://prove2.me/submissions/03627ae3-56a3-4184-a06d-8f73741c4e33

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 306, k = 46665 := by
  rw [sum_range_id]
