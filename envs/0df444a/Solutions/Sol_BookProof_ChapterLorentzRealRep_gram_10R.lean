-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.gram_10R
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:54:41.190986+00:00
-- url     : https://prove2.me/submissions/95251c8c-7ab7-45c0-8f58-cb47496597ef

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.gram_10R
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Theorems.Thm_BookProof_ChapterLorentzRealRep_gram_10
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_mul
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_transpose
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_trace
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ i j : Fin 6, ((b10R i)ᵀ * b10R j).trace = if i = j then (4 : ℝ) else 0 := by

  intro i j;    rw [ b10R, b10R, ← castR_transpose, ← castR_mul, castR_trace, gram_10 ] ; split_ifs
      <;> norm_num;
