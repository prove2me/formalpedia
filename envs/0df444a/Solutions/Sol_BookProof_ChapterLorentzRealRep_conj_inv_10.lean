-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.conj_inv_10
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:50:20.936737+00:00
-- url     : https://prove2.me/submissions/6aac0fa7-a430-473b-80cc-13d00c512ade

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.conj_inv_10
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ S ∈ Omega, ∀ i, S * b10 i * cinv S ∈ SB10 := by
 decide
