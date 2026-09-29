-- Prove2me | solution 1 for FiniteTriangular.sum_range_166
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:20:39.297988+00:00
-- url     : https://prove2.me/submissions/b32d6baf-17d2-4d00-974b-8979bf0a0605

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 166, k = 13695 := by
  rw [sum_range_id]
