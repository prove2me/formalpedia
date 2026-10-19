-- Prove2me | solution 1 for BookProof.ChapterG3.eventProj_inter
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T13:29:26.708668+00:00
-- url     : https://prove2.me/submissions/5c576caa-e43b-42cc-bf3b-d3b96d120f55

-- Generated from ChapterG3.lean — solution of BookProof.ChapterG3.eventProj_inter
import Mathlib
import Definitions.Def_ChapterG3
import Definitions.Def_ChapterConservativeDiagonal
open BookProof.ChapterG3



open MeasureTheory
open scoped ENNReal
open BookProof.ConservativeDiagonal



variable {X : Type*}

variable {X : Type*}

set_option maxHeartbeats 1000000 in
theorem solution (A B : Set X) :
    BookProof.ChapterG3.eventProj (A ∩ B) = BookProof.ChapterG3.eventProj A * BookProof.ChapterG3.eventProj B := by

  funext x; by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
    simp [BookProof.ChapterG3.eventProj, Set.indicator, hA, hB]
