-- Prove2me | solution 1 for ChapterTotalVariance.between_le_variance
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T16:34:15.875357+00:00
-- url     : https://prove2.me/submissions/18245f53-14c6-4e87-ac0e-8e8b2c9ac3e6

-- Generated from ChapterTotalVariance.lean — solution of ChapterTotalVariance.between_le_variance
import Mathlib
import Definitions.Def_ChapterTotalVariance
import Theorems.Thm_ChapterTotalVariance_total_variance
import Theorems.Thm_ChapterTotalVariance_within_nonneg
import Definitions.Def_ChapterA4
open ChapterTotalVariance




open scoped BigOperators
open Finset

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

variable {Ω κ : Type*} [Fintype Ω] [DecidableEq κ]

set_option maxHeartbeats 1000000 in
theorem solution [Finite κ] (w : Ω → ℝ) (X : Ω → κ) (Y : Ω → ℝ)
    (hw : ∀ ω, 0 ≤ w ω) :
    between w X Y ≤ variance w Y := by

  rw [total_variance w X Y hw]
  linarith [within_nonneg w X Y hw]
