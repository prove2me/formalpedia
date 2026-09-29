-- Prove2me | solution 1 for FiniteTriangular.sum_range_1131
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:32:22.786949+00:00
-- url     : https://prove2.me/submissions/f944e1b9-c375-4fff-9381-72646186c0e5

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1131, k = 639015 := by
  rw [sum_range_id]
