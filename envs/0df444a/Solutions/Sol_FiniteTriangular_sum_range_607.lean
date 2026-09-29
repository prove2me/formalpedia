-- Prove2me | solution 1 for FiniteTriangular.sum_range_607
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:44:56.98853+00:00
-- url     : https://prove2.me/submissions/5c4647df-0774-45d5-986d-aa68a915f526

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 607, k = 183921 := by
  rw [sum_range_id]
