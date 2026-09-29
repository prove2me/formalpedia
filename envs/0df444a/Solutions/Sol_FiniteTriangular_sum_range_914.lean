-- Prove2me | solution 1 for FiniteTriangular.sum_range_914
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:51:58.46135+00:00
-- url     : https://prove2.me/submissions/665a1897-45b4-4a0a-a391-2f2ee6fe1abd

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 914, k = 417241 := by
  rw [sum_range_id]
