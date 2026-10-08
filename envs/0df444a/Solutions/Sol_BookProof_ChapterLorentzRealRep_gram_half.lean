-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.gram_half
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:54:33.116318+00:00
-- url     : https://prove2.me/submissions/7e5464da-80b0-4471-a038-1454bb599859

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.gram_half
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ i j : Fin 4, ((bHalf i)ᵀ * bHalf j).trace = if i = j then 4 else 0 := by

  decide
