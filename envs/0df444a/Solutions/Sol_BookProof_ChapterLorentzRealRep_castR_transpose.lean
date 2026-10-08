-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.castR_transpose
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:54:37.485001+00:00
-- url     : https://prove2.me/submissions/4c8a020e-7e7b-4b5d-ab5d-4894302d55a1

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.castR_transpose
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin 4) (Fin 4) ℤ) : castR (Aᵀ) = (castR A)ᵀ := by

  ext i j; simp [castR, RingHom.mapMatrix_apply, Matrix.transpose_apply, Matrix.map_apply]
