-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.bPsR_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:45:57.133974+00:00
-- url     : https://prove2.me/submissions/db9b9411-3ae2-4014-a1ed-fec83e999a60

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.bPsR_linearIndependent
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Theorems.Thm_BookProof_ChapterLorentzRealRep_gram_psR
import Theorems.Thm_BookProof_ChapterLorentzRealRep_linIndep_of_gram
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : LinearIndependent ℝ bPsR := linIndep_of_gram bPsR gram_psR
