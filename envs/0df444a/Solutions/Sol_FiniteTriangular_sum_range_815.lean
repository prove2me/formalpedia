-- Prove2me | solution 1 for FiniteTriangular.sum_range_815
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:30:20.280706+00:00
-- url     : https://prove2.me/submissions/7dc1dfca-ebec-4aef-b9e0-00eeabfca960

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 815, k = 331705 := by
  rw [sum_range_id]
