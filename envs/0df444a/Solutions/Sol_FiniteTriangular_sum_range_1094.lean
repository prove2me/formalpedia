-- Prove2me | solution 1 for FiniteTriangular.sum_range_1094
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:24:01.698532+00:00
-- url     : https://prove2.me/submissions/128e87da-5eeb-46fb-b8dd-098a5835e762

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1094, k = 597871 := by
  rw [sum_range_id]
