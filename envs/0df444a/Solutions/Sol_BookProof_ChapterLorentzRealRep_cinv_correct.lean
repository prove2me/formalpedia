-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.cinv_correct
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:50:06.28699+00:00
-- url     : https://prove2.me/submissions/b477fe3a-0765-4e50-ab2b-ef3fa8709fea

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.cinv_correct
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ S ∈ Omega, S * cinv S = 1 := by
 decide
