-- Prove2me | solution 1 for FiniteTriangular.sum_range_598
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:43:11.214894+00:00
-- url     : https://prove2.me/submissions/80b99575-ef11-4d88-82a1-aa54a91f46fa

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 598, k = 178503 := by
  rw [sum_range_id]
