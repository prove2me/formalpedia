-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.gram_halfR
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:54:40.020976+00:00
-- url     : https://prove2.me/submissions/1d897972-5110-44bf-ab66-0ee032bab45c

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.gram_halfR
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Theorems.Thm_BookProof_ChapterLorentzRealRep_gram_half
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_mul
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_transpose
import Theorems.Thm_BookProof_ChapterLorentzRealRep_castR_trace
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution :
    ∀ i j : Fin 4, ((bHalfR i)ᵀ * bHalfR j).trace = if i = j then (4 : ℝ) else 0 := by

  intro i j;    rw [ show bHalfR i = castR ( bHalf i ) from rfl, show bHalfR j = castR ( bHalf j )
      from rfl ] ;    rw [ ← castR_transpose, ← castR_mul, castR_trace ] ; norm_num [ gram_half ] ;
