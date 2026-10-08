-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.cinv_correct_left
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:50:07.419842+00:00
-- url     : https://prove2.me/submissions/1b26e5be-fccb-4b0d-8ce7-9a4be39da1a7

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.cinv_correct_left
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ S ∈ Omega, cinv S * S = 1 := by
 decide
