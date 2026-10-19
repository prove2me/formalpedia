-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornFiberStabilizer.boolSign_pm_inc
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-17T20:38:49.419536+00:00
-- url     : https://prove2.me/submissions/5b165049-3f0e-4b8c-a436-daccad431d6b

-- Generated from ChapterFreeFieldBornFiberStabilizer.lean — solution of BookProof.ChapterFreeFieldBornFiberStabilizer.boolSign_pm_inc
import Mathlib
import Definitions.Def_ChapterFreeFieldBornFiberStabilizer
import Definitions.Def_ChapterFreeFieldBorn
import Definitions.Def_ChapterFreeFieldBornQuotient
import Definitions.Def_ChapterFreeFieldBornSignGauge
import Definitions.Def_ChapterFreeFieldBornFiberCardGeneral
import Definitions.Def_ChapterFreeFieldBornFiberBounds
open BookProof.ChapterFreeFieldBornFiberStabilizer



open MeasureTheory
open BookProof.ChapterFreeFieldBorn
open BookProof.ChapterFreeFieldBornQuotient
open BookProof.ChapterFreeFieldBornSignGauge
open BookProof.ChapterFreeFieldBornFiberCardGeneral
open BookProof.ChapterFreeFieldBornFiberBounds


variable {n : ℕ}

variable {n : ℕ}

set_option maxHeartbeats 1000000 in
theorem solution (b : Fin n → Bool) (k : Fin n) :
    boolSign b k = 1 ∨ boolSign b k = -1 := by

  unfold boolSign; split_ifs <;> simp
