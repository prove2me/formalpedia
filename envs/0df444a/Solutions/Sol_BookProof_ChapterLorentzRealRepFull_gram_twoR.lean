-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepFull.gram_twoR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:06:49.960864+00:00
-- url     : https://prove2.me/submissions/f48b927c-3859-40f0-b8f8-b2ba0feb5584

-- Generated from ChapterLorentzRealRepFull.lean — solution of BookProof.ChapterLorentzRealRepFull.gram_twoR
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
import Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_two
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
theorem solution : ∀ i j : Fin 2, ((w2R i)ᵀ * w2R j).trace = if i = j then (4 : ℝ) else 0 := by

  intro i j
  rw [w2R, w2R, ← castR_transpose, ← castR_mul, castR_trace, gram_two]
  split_ifs <;> norm_num
