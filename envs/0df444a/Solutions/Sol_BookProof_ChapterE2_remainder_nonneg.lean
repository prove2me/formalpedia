-- Prove2me | solution 1 for BookProof.ChapterE2.remainder_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:29:25.591033+00:00
-- url     : https://prove2.me/submissions/8b54e2b4-7280-4e9a-8eaf-d81d1d9b260e

-- Generated from ChapterE2.lean — solution of BookProof.ChapterE2.remainder_nonneg
import Mathlib
import Definitions.Def_ChapterE2
open BookProof.ChapterE2



open scoped BigOperators
open Finset

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (N : ℕ) : 0 ≤ remainder θ N := Finset.prod_nonneg (fun _ _ => sq_nonneg _)
