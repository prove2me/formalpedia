-- Prove2me | solution 1 for FiniteTriangular.sum_range_510
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:22:23.029226+00:00
-- url     : https://prove2.me/submissions/28c1ad8f-bcc8-4403-acc0-e191c0d3d438

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 510, k = 129795 := by
  rw [sum_range_id]
