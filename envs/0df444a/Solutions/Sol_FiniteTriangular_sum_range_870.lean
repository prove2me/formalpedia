-- Prove2me | solution 1 for FiniteTriangular.sum_range_870
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:42:00.141239+00:00
-- url     : https://prove2.me/submissions/43122ee3-66c8-445e-b168-786dfe0fa4c7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 870, k = 378015 := by
  rw [sum_range_id]
