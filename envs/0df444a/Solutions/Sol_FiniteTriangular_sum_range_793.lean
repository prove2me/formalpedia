-- Prove2me | solution 1 for FiniteTriangular.sum_range_793
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:26:43.053818+00:00
-- url     : https://prove2.me/submissions/8f166c54-77cb-4386-801a-d2468d057891

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 793, k = 314028 := by
  rw [sum_range_id]
