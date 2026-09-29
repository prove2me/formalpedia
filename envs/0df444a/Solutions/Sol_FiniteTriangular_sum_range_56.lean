-- Prove2me | solution 1 for FiniteTriangular.sum_range_56
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-09-24T19:19:16.140985+00:00
-- url     : https://prove2.me/submissions/605c7cdf-6092-4b7d-b039-b64c231d98ea

import Mathlib
open Finset

theorem solution : ∑ k ∈ range 56, k = 1540 := by
  decide
