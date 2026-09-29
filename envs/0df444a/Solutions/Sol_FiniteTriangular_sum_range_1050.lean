-- Prove2me | solution 1 for FiniteTriangular.sum_range_1050
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-26T17:14:59.661633+00:00
-- url     : https://prove2.me/submissions/96f05d65-7622-41ae-b071-9d0f0d7c521d

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 1050, k = 550725 := by
  rw [sum_range_id]
