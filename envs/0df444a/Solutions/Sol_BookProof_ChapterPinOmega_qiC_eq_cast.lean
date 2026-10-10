-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qiC_eq_cast
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:23.041136+00:00
-- url     : https://prove2.me/submissions/73c9abe4-3dbd-4750-ad43-7f88f3decc1b

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qiC_eq_cast
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qiC = (Int.castRingHom ℂ).mapMatrix qi := rfl
