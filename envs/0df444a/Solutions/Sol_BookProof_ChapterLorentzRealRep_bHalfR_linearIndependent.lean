-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.bHalfR_linearIndependent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-09T08:45:42.979545+00:00
-- url     : https://prove2.me/submissions/d7e0216e-e227-431d-950b-4aec45693844

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.bHalfR_linearIndependent
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
import Theorems.Thm_BookProof_ChapterLorentzRealRep_gram_halfR
import Theorems.Thm_BookProof_ChapterLorentzRealRep_linIndep_of_gram
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : LinearIndependent ℝ bHalfR := linIndep_of_gram bHalfR gram_halfR
