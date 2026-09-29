-- Prove2me | solution 1 for FiniteTriangular.sum_range_1032
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T10:45:58.748326+00:00
-- url     : https://prove2.me/submissions/dd8ab697-2876-4bc6-b3a8-9ab3fd52c6ec

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1032, k = 531996 := by
  rw [sum_range_id]
