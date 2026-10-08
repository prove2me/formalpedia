-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignAction.boolFlip_involutive
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-05T10:57:44.548141+00:00
-- url     : https://prove2.me/submissions/3f828b13-0889-43f4-8c37-af1ceb0e8dbf

-- Generated from ChapterFreeFieldBornSignAction.lean — solution of BookProof.ChapterFreeFieldBornSignAction.boolFlip_involutive
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignAction
open BookProof.ChapterFreeFieldBornSignAction



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornSignGauge


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) (x : EuclideanSpace ℝ (Fin n)) :
    boolFlip b (boolFlip b x) = x := by

  ext k; simp only [boolFlip_apply]; split_ifs <;> ring
