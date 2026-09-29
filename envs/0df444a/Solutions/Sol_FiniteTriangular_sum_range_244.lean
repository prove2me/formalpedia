-- Prove2me | solution 1 for FiniteTriangular.sum_range_244
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:59:25.243053+00:00
-- url     : https://prove2.me/submissions/4d551411-df2b-4de1-a586-a61e94ec9a8e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 244, k = 29646 := by
  rw [sum_range_id]
