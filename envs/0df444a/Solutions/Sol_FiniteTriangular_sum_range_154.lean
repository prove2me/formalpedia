-- Prove2me | solution 1 for FiniteTriangular.sum_range_154
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:17:47.32882+00:00
-- url     : https://prove2.me/submissions/a53406c4-89d2-4803-912b-43e272c1e3e1

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 154, k = 11781 := by
  rw [sum_range_id]
