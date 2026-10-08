-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.gram_ps
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:54:35.11879+00:00
-- url     : https://prove2.me/submissions/84a1491b-070a-4ec4-a276-ca156a9b5249

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.gram_ps
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ i j : Fin 4, ((bPs i)ᵀ * bPs j).trace = if i = j then 4 else 0 := by

  decide
