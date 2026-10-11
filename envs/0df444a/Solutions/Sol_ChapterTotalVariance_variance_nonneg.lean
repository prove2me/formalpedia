-- Prove2me | solution 1 for ChapterTotalVariance.variance_nonneg
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:13.086136+00:00
-- url     : https://prove2.me/submissions/a4edb978-35ae-4a3d-b2cb-76347807907a

-- Generated from ChapterTotalVariance.lean — solution of ChapterTotalVariance.variance_nonneg
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Definitions.Def_ChapterA4
open ChapterTotalVariance




open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

set_option maxHeartbeats 1000000 in
theorem solution (w Y : Ω → ℝ) (hw : ∀ ω, 0 ≤ w ω) :
    0 ≤ variance w Y := by

  refine Finset.sum_nonneg (fun ω _ => ?_)
  exact mul_nonneg (hw ω) (sq_nonneg _)
