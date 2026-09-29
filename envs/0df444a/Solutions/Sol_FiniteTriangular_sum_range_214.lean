-- Prove2me | solution 1 for FiniteTriangular.sum_range_214
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:51:44.087116+00:00
-- url     : https://prove2.me/submissions/a4d38392-cdcf-4fbd-bd3c-ee3cb8443a7c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 214, k = 22791 := by
  rw [sum_range_id]
