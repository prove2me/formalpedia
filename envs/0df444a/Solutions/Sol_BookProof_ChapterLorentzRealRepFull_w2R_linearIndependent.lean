-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRepFull.w2R_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T21:07:11.653983+00:00
-- url     : https://prove2.me/submissions/0221152b-2be8-4e47-acc2-723a0296d02b

-- Generated from ChapterLorentzRealRepFull.lean — solution of BookProof.ChapterLorentzRealRepFull.w2R_linearIndependent
import Mathlib
import Definitions.Def_ChapterLorentzRealRepFull
import Theorems.Thm_BookProof_ChapterLorentzRealRepFull_gram_twoR
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
theorem solution : LinearIndependent ℝ w2R := linIndep_of_gram w2R gram_twoR
