-- Prove2me | solution 1 for FiniteTriangular.sum_range_501
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:20:35.950543+00:00
-- url     : https://prove2.me/submissions/506ba868-05b4-4039-b4ab-f498790f375d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 501, k = 125250 := by
  rw [sum_range_id]
