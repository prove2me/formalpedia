-- Prove2me | solution 1 for FiniteTriangular.sum_range_71
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:33:06.665368+00:00
-- url     : https://prove2.me/submissions/2fb6c1d8-a4fc-4dee-9c42-8c2c4dc5653f

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 71, k = 2485 := by
  decide
