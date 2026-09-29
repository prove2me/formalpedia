-- Prove2me | solution 1 for FiniteTriangular.sum_range_592
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:41:36.887112+00:00
-- url     : https://prove2.me/submissions/9bb1f551-2f8b-440f-9301-f961043fcc82

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 592, k = 174936 := by
  rw [sum_range_id]
