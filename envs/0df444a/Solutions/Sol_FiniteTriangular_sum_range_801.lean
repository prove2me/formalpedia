-- Prove2me | solution 1 for FiniteTriangular.sum_range_801
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:28:28.143797+00:00
-- url     : https://prove2.me/submissions/5fc5fdb9-2cda-4a25-b69a-66250cb2e946

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 801, k = 320400 := by
  rw [sum_range_id]
