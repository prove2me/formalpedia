-- Prove2me | solution 1 for FiniteTriangular.sum_range_194
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T07:47:32.266986+00:00
-- url     : https://prove2.me/submissions/f4220040-c976-44c9-a1cb-8db1da627b2e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 194, k = 18721 := by
  rw [sum_range_id]
