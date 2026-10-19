-- Prove2me | solution 1 for BookProof.ChapterGaugeUnconstrainedSpectrum.exists_eigenvalue_of_isFunctionOfSpectrum
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T07:39:38.074432+00:00
-- url     : https://prove2.me/submissions/3cb32fc1-4e7f-496f-a083-4854a30d4e06

-- Generated from ChapterGaugeUnconstrainedSpectrum.lean — solution of BookProof.ChapterGaugeUnconstrainedSpectrum.exists_eigenvalue_of_isFunctionOfSpectrum
import Mathlib
import Definitions.Def_ChapterGaugeUnconstrainedSpectrum
import Theorems.Thm_BookProof_ChapterGaugeUnconstrainedSpectrum_diagOp_basisVec
open BookProof.ChapterGaugeUnconstrainedSpectrum




variable {X : Type*}

variable {X : Type*}

set_option maxHeartbeats 1000000 in
theorem solution [DecidableEq X] {T : Op X}
    (hT : IsFunctionOfSpectrum T) (y : X) :
    ∃ c : ℂ, T (basisVec y) = c • basisVec y := by

  obtain ⟨d, rfl⟩ := hT
  exact ⟨d y, diagOp_basisVec d y⟩
