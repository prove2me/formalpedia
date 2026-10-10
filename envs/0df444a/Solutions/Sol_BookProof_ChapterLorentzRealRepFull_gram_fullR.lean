-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepFull.gram_fullR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:08:55.991269+00:00
-- url     : https://prove2.me/submissions/07c1872b-21d9-46b1-abdf-b1c7e9d7da09

-- Generated from ChapterLorentzRealRepFull.lean — solution of BookProof.ChapterLorentzRealRepFull.gram_fullR
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
import Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_full
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
theorem solution :
    ∀ i j : Fin 16, ((bFullR i)ᵀ * bFullR j).trace = if i = j then (4 : ℝ) else 0 := by

  intro i j
  rw [bFullR, bFullR, ← castR_transpose, ← castR_mul, castR_trace, gram_full]
  split_ifs <;> norm_num
