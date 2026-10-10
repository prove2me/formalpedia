-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepSum.bAllR_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:17:45.675826+00:00
-- url     : https://prove2.me/submissions/c760f25f-08e9-412f-ab91-d8bc5f5cf745

-- Generated from ChapterLorentzRealRepSum.lean — solution of BookProof.ChapterLorentzRealRepSum.bAllR_linearIndependent
import Mathlib
import Definitions.Def_ChapterLorentzRealRepSum
import Theorems.Thm_BookProof_ChapterLorentzRealRepSum_gram_allR
import Theorems.Thm_BookProof_ChapterLorentzRealRep_linIndep_of_gram
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open Module

set_option maxHeartbeats 1000000 in
theorem solution : LinearIndependent ℝ bAllR := linIndep_of_gram bAllR gram_allR
