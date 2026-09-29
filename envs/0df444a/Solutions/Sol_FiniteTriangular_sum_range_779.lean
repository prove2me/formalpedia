-- Prove2me | solution 1 for FiniteTriangular.sum_range_779
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-25T11:23:22.974048+00:00
-- url     : https://prove2.me/submissions/2be03193-05b4-4937-b848-e09805804863

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 779, k = 303031 := by
  rw [sum_range_id]
