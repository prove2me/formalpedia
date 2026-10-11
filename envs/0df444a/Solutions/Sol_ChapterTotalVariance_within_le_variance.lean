-- Prove2me | solution 1 for ChapterTotalVariance.within_le_variance
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:14.434113+00:00
-- url     : https://prove2.me/submissions/6add9728-c459-4400-8591-62d5c03f8828

-- Generated from ChapterTotalVariance.lean — solution of ChapterTotalVariance.within_le_variance
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Theorems.Thm_ChapterTotalVariance_total_variance
import Theorems.Thm_ChapterTotalVariance_between_nonneg
import Definitions.Def_ChapterA4
open ChapterTotalVariance




open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

set_option maxHeartbeats 1000000 in
theorem solution [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) :
    within w X Y ≤ variance w Y := by

  rw [total_variance w X Y hw]
  linarith [between_nonneg w X Y hw]
