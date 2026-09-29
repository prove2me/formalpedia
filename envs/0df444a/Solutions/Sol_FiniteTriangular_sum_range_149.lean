-- Prove2me | solution 1 for FiniteTriangular.sum_range_149
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T20:17:43.918981+00:00
-- url     : https://prove2.me/submissions/5015a1f5-0368-4a5e-8697-3604db659357

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 149, k = 11026 := by
  rw [sum_range_id]
