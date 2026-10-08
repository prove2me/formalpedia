-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignAction.flipVec_pm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:55:24.787073+00:00
-- url     : https://prove2.me/submissions/6cda4d5d-ceed-4a6f-9605-8b899736c7a3

-- Generated from ChapterFreeFieldBornSignAction.lean — solution of BookProof.ChapterFreeFieldBornSignAction.flipVec_pm
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) (k : Fin n) :
    flipVec b k = 1 ∨ flipVec b k = -1 := by

  unfold flipVec; split_ifs <;> simp
