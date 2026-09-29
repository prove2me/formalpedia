-- Prove2me | solution 1 for FiniteTriangular.sum_range_131
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:13:26.787582+00:00
-- url     : https://prove2.me/submissions/a9eec91e-b1dd-4b4e-bff3-843de5fbaeda

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 131, k = 8515 := by
  rw [sum_range_id]
