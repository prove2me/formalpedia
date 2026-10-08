-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.conj_inv_ps
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:50:44.97032+00:00
-- url     : https://prove2.me/submissions/2ab3f845-b2c6-4862-9827-935fa9377f2c

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.conj_inv_ps
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ S ∈ Omega, ∀ i, S * bPs i * cinv S ∈ SBPs := by
 decide
