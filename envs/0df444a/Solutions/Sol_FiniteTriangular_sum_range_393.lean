-- Prove2me | solution 1 for FiniteTriangular.sum_range_393
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T09:48:52.450317+00:00
-- url     : https://prove2.me/submissions/a19b4507-ea54-4915-884b-0620b538d380

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 393, k = 77028 := by
  rw [sum_range_id]
