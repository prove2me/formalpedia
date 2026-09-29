-- Prove2me | solution 1 for FiniteTriangular.sum_range_978
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:35:10.577318+00:00
-- url     : https://prove2.me/submissions/b62b9bca-2d2d-47b5-b91c-441789869c68

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 978, k = 477753 := by
  rw [sum_range_id]
