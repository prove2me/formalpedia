-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.conj_inv_half
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:50:19.773071+00:00
-- url     : https://prove2.me/submissions/4f398be1-4710-4f2c-bf95-a94dc4b42357

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.conj_inv_half
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ S ∈ Omega, ∀ i, S * bHalf i * cinv S ∈ SBHalf := by
 decide
