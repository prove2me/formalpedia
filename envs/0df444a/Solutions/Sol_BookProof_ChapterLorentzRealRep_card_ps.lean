-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.card_ps
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:54:32.03882+00:00
-- url     : https://prove2.me/submissions/b2782e02-5929-4825-8e8a-5ce251391c87

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.card_ps
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : (Finset.univ.image bPs).card = 4 := by
 decide
