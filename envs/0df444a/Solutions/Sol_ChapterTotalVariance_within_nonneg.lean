-- Prove2me | solution 1 for ChapterTotalVariance.within_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:10.338632+00:00
-- url     : https://prove2.me/submissions/110c5fd0-e407-4007-9df7-14f9b4b2e8f9

-- Generated from ChapterTotalVariance.lean — solution of ChapterTotalVariance.within_nonneg
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance




open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

set_option maxHeartbeats 1000000 in
theorem solution (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) :
    0 ≤ within w X Y := by

  refine Finset.sum_nonneg (fun ω _ => ?_)
  exact mul_nonneg (hw ω) (sq_nonneg _)
