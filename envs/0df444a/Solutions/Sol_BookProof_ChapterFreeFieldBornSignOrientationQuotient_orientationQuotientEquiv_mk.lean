-- Prove2me | solution 1 for BookProof.ChapterFreeFieldBornSignOrientationQuotient.orientationQuotientEquiv_mk
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-16T23:58:05.930986+00:00
-- url     : https://prove2.me/submissions/9b850906-75ef-4d02-8d39-5c33341fe531

-- Generated from ChapterFreeFieldBornSignOrientationQuotient.lean — solution of BookProof.ChapterFreeFieldBornSignOrientationQuotient.orientationQuotientEquiv_mk
import Mathlib
import Definitions.Def_ChapterFreeFieldBornSignOrientationQuotient
import Definitions.Def_ChapterFreeFieldBornSignHom
import Definitions.Def_ChapterFreeFieldBornSignOrientationSubgroup
open BookProof.ChapterFreeFieldBornSignOrientationQuotient



open BookProof.ChapterFreeFieldBornSignHom
open BookProof.ChapterFreeFieldBornSignOrientationSubgroup

set_option maxHeartbeats 1000000 in
theorem solution (n : ℕ) (b : Fin (n + 1) → Bool) :
    orientationQuotientEquiv n (QuotientAddGroup.mk b) =
      orientationCharacter (n + 1) b := by

  convert QuotientAddGroup.kerLift_mk (orientationCharacter (n + 1)) b using 1
  rfl
