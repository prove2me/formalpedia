-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.conjL_apply
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:56:10.101087+00:00
-- url     : https://prove2.me/submissions/c530619e-8bcc-4a0a-8ffa-7552efbe5d92

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.conjL_apply
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution (S T A : Matrix (Fin 4) (Fin 4) ℝ) : conjL S T A = S * A * T := by

  simp [conjL, mul_assoc]
