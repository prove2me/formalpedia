-- Prove2me | solution 1 for FiniteTriangular.sum_range_826
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:33:40.404583+00:00
-- url     : https://prove2.me/submissions/5fe81405-afdc-492b-a554-7151595a100e

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 826, k = 340725 := by
  rw [sum_range_id]
