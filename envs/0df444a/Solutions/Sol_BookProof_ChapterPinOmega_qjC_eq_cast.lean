-- Prove2me | solution 1 for BookProof.ChapterPinOmega.qjC_eq_cast
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-10T10:00:24.074845+00:00
-- url     : https://prove2.me/submissions/cd9acb48-e736-401d-855a-0a07ae78c601

-- Generated from ChapterPinOmega.lean — solution of BookProof.ChapterPinOmega.qjC_eq_cast
import Mathlib
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinDoubleCover
open BookProof.ChapterPinOmega



open Matrix


open BookProof.ChapterA3

set_option maxHeartbeats 1000000 in
theorem solution : qjC = (Int.castRingHom ℂ).mapMatrix qj := by

  rw [qjC, qj, map_neg, map_mul]; rfl
