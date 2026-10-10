-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepSum.gram_10PsR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:15:01.227566+00:00
-- url     : https://prove2.me/submissions/f18824cb-1872-4165-aa14-f0f6b8390af7

-- Generated from ChapterLorentzRealRepSum.lean — solution of BookProof.ChapterLorentzRealRepSum.gram_10PsR
import Mathlib
import Definitions.Def_ChapterLorentzRealRepSum
import Theorems.Thm_BookProof_ChapterLorentzRealRepSum_gram_10Ps
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_mul
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_trace
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_transpose
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open Module

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (i : Fin 6) (j : Fin 4), ((b10R i)ᵀ * bPsR j).trace = (0 : ℝ) := by

  intro i j
  rw [b10R, bPsR, ← castR_transpose, ← castR_mul, castR_trace, gram_10Ps]
  norm_num
