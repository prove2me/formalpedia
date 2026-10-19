-- Prove2me | solution 1 for BookProof.ChapterG3.eventProj_idem
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T13:29:25.712774+00:00
-- url     : https://prove2.me/submissions/8e1ad44a-a506-4b3a-8caf-828daa3d6358

-- Generated from ChapterG3.lean — solution of BookProof.ChapterG3.eventProj_idem
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
theorem solution (A : Set X) : BookProof.ChapterG3.eventProj A * BookProof.ChapterG3.eventProj A = BookProof.ChapterG3.eventProj A := by

  funext x; by_cases h : x ∈ A <;> simp [BookProof.ChapterG3.eventProj, Set.indicator, h]
