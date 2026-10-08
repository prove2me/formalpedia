-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.gram_psR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:56:08.186309+00:00
-- url     : https://prove2.me/submissions/aeccfd35-b0cc-4666-8368-86e86c1df356

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.gram_psR
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Theorems.Thm_BookProof_ChapterLorentzRealRep_gram_ps
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_mul
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_transpose
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_trace
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ i j : Fin 4, ((bPsR i)ᵀ * bPsR j).trace = if i = j then (4 : ℝ) else 0 := by

  intros i j;    rw [ show bPsR i = castR ( bPs i ) from rfl, show bPsR j = castR ( bPs j ) from
      rfl, ← castR_transpose, ← castR_mul, castR_trace ] ;
  split_ifs <;> simp_all [ gram_ps ]
