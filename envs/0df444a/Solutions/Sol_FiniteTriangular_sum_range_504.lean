-- Prove2me | solution 1 for FiniteTriangular.sum_range_504
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:20:37.689012+00:00
-- url     : https://prove2.me/submissions/33b5a9cc-f7ec-4744-91cb-820a4cd80338

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 504, k = 126756 := by
  rw [sum_range_id]
