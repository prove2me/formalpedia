-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepFull.gram_two_PsR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:07:07.727889+00:00
-- url     : https://prove2.me/submissions/09edcccd-c20a-4e43-9651-61db4e3f83b5

-- Generated from ChapterLorentzRealRepFull.lean — solution of BookProof.ChapterLorentzRealRepFull.gram_two_PsR
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
import Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_two_Ps
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_mul
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_trace
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_transpose
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepFull



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum
open Module

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (i : Fin 2) (j : Fin 4), ((w2R i)ᵀ * bPsR j).trace = (0 : ℝ) := by

  intro i j
  rw [w2R, bPsR, ← castR_transpose, ← castR_mul, castR_trace, gram_two_Ps]
  norm_num
