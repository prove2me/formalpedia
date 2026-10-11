-- Prove2me | solution 1 for BookProof.SmOneParticle.smDimB_eq_card
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-10-11T10:21:15.212384+00:00
-- url     : https://prove2.me/submissions/680ad016-d851-484f-9848-d56b61be6a4d

-- Generated from ChapterSmOneParticle.lean — solution of BookProof.SmOneParticle.smDimB_eq_card
import Mathlib
import Definitions.Def_ChapterSmOneParticle
open BookProof.SmOneParticle

set_option maxHeartbeats 1000000 in
theorem solution : smDimB = Fintype.card SmCoord := card_smCoord.symm
