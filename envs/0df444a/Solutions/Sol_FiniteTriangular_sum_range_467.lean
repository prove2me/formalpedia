-- Prove2me | solution 1 for FiniteTriangular.sum_range_467
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:13:50.291074+00:00
-- url     : https://prove2.me/submissions/a60d7015-e20b-4fb4-9a4d-f17108f9236d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 467, k = 108811 := by
  rw [sum_range_id]
