-- Prove2me | solution 1 for BookProof.ChapterG3.eventProj_comm
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-18T12:59:56.986793+00:00
-- url     : https://prove2.me/submissions/0d945f6b-e6da-4564-94aa-9eeee366918b

-- Generated from ChapterG3.lean — solution of BookProof.ChapterG3.eventProj_comm
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
    eventProj A * eventProj B = eventProj B * eventProj A := by

  ring
