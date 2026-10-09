-- Prove2me | solution 1 for BookProof.ChapterE2.remainder_le_one
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:29:39.111694+00:00
-- url     : https://prove2.me/submissions/f616b6f9-fae5-4b5d-874d-acae0979383a

-- Generated from ChapterE2.lean — solution of BookProof.ChapterE2.remainder_le_one
import Mathlib
import Definitions.Def_ChapterE2
open BookProof.ChapterE2



open scoped BigOperators
open Finset

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (N : ℕ) : remainder θ N ≤ 1 := by

  exact Finset.prod_le_one ( fun _ _ => sq_nonneg _ ) fun _ _ => Real.sin_sq_le_one _
