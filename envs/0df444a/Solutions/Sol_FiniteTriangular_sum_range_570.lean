-- Prove2me | solution 1 for FiniteTriangular.sum_range_570
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T10:38:02.907112+00:00
-- url     : https://prove2.me/submissions/5cb0c253-151b-4aa3-b7c5-ae999cddaa06

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 570, k = 162165 := by
  rw [sum_range_id]
