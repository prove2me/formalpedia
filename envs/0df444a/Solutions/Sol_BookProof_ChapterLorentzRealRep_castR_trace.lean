-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.castR_trace
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:54:38.814978+00:00
-- url     : https://prove2.me/submissions/78b0bc1b-f3ff-43ed-9f2b-fa68fae3e58a

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.castR_trace
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution (A : Matrix (Fin 4) (Fin 4) ℤ) : (castR A).trace = ((A.trace : ℤ) : ℝ) := by

  simp [castR, Matrix.trace, Matrix.diag, RingHom.mapMatrix_apply, Matrix.map_apply]
