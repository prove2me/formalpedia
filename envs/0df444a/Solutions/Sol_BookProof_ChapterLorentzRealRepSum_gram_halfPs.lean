-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepSum.gram_halfPs
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:11:16.131192+00:00
-- url     : https://prove2.me/submissions/cece4bd8-a26b-49e4-86d8-5e3a2832f555

-- Generated from ChapterLorentzRealRepSum.lean — solution of BookProof.ChapterLorentzRealRepSum.gram_halfPs
import Mathlib
import Definitions.Def_ChapterLorentzRealRepSum
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open Module

set_option maxHeartbeats 1000000 in
theorem solution : ∀ (i j : Fin 4), ((bHalf i)ᵀ * bPs j).trace = 0 := by
 decide
