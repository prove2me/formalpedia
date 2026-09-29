-- Prove2me | solution 1 for FiniteTriangular.sum_range_262
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T08:11:16.107214+00:00
-- url     : https://prove2.me/submissions/dca32c83-b3d2-42ec-9e0d-ad5e9fbe2fa7

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 262, k = 34191 := by
  rw [sum_range_id]
