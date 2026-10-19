-- Prove2me | solution 1 for BookProof.ChapterG3.eventProj_union
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T13:30:48.232188+00:00
-- url     : https://prove2.me/submissions/e0dd9472-97aa-460b-b3b2-312251297d64

-- Generated from ChapterG3.lean — solution of BookProof.ChapterG3.eventProj_union
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
    BookProof.ChapterG3.eventProj (A ∪ B) = BookProof.ChapterG3.eventProj A + BookProof.ChapterG3.eventProj B - BookProof.ChapterG3.eventProj A * BookProof.ChapterG3.eventProj B := by

  funext x; by_cases hA : x ∈ A <;> by_cases hB : x ∈ B <;>
    simp [BookProof.ChapterG3.eventProj, Set.indicator, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, hA, hB]
