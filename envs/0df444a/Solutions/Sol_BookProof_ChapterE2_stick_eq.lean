-- Prove2me | solution 1 for BookProof.ChapterE2.stick_eq
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T06:28:58.245996+00:00
-- url     : https://prove2.me/submissions/faa3efab-e2b4-45ec-950d-6585c1ddadcc

-- Generated from ChapterE2.lean — solution of BookProof.ChapterE2.stick_eq
import Mathlib
import Definitions.Def_ChapterE2
open BookProof.ChapterE2



open scoped BigOperators
open Finset

set_option maxHeartbeats 1000000 in
theorem solution (θ : ℕ → ℝ) (n : ℕ) :
    stick θ n = remainder θ n * Real.cos (θ n) ^ 2 := by

  rfl
