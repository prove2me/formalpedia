-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qkC_eq_cast
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:25.053218+00:00
-- url     : https://prove2.me/submissions/bebd861f-e7d6-4607-a058-c43173fb793d

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qkC_eq_cast
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qkC = (Int.castRingHom ℂ).mapMatrix qk := rfl
