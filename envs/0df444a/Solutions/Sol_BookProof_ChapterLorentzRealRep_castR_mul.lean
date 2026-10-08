-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.castR_mul
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:54:36.280526+00:00
-- url     : https://prove2.me/submissions/eaadeeaf-8cb1-4475-a720-5f7eb8af1604

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.castR_mul
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution (A B : Matrix (Fin 4) (Fin 4) ℤ) : castR (A * B) = castR A * castR B := map_mul ((Int.castRingHom ℝ).mapMatrix) A B
