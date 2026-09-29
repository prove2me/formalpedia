-- Prove2me | solution 1 for FiniteTriangular.sum_range_204
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:49:28.710977+00:00
-- url     : https://prove2.me/submissions/b95adc14-e018-4034-be64-9c7d0eff288c

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 204, k = 20706 := by
  rw [sum_range_id]
