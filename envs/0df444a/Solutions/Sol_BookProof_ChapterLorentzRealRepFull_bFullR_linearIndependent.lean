-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepFull.bFullR_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:09:21.429951+00:00
-- url     : https://prove2.me/submissions/ae64f84c-ff9b-43d4-9e00-736684c138ee

-- Generated from ChapterLorentzRealRepFull.lean — solution of BookProof.ChapterLorentzRealRepFull.bFullR_linearIndependent
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
import Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_fullR
import Theorems.Thm_BookProof_ChapterLorentzRealRep_linIndep_of_gram
import Definitions.Def_ChapterA3
import Definitions.Def_ChapterPinOmega
import Definitions.Def_ChapterLorentzRealRep
import Definitions.Def_ChapterLorentzRealRepSum
open BookProof.ChapterLorentzRealRepFull



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega BookProof.ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRepSum
open Module

set_option maxHeartbeats 1000000 in
theorem solution : LinearIndependent ℝ bFullR := linIndep_of_gram bFullR gram_fullR
