-- Prove2me | solution 1 for BookProof.ChapterLorentzRealRep.gram_10
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-07T16:54:34.218667+00:00
-- url     : https://prove2.me/submissions/8fae0480-5e4d-4a00-a082-3d9f21a64cc8

-- Generated from ChapterLorentzRealRep.lean — solution of BookProof.ChapterLorentzRealRep.gram_10
import Mathlib
import Definitions.Def_ChapterLorentzRealRep
open BookProof.ChapterLorentzRealRep



open Matrix


open BookProof.ChapterA3 BookProof.ChapterPinOmega

set_option maxHeartbeats 1000000 in
theorem solution : ∀ i j : Fin 6, ((b10 i)ᵀ * b10 j).trace = if i = j then 4 else 0 := by

  decide
