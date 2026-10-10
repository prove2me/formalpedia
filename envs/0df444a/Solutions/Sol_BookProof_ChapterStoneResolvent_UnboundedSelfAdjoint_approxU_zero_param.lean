-- Prove2me | solution 1 for BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint.approxU_zero_param
-- status  : ACCEPTED   (prove)
-- author  : @carlok
-- created : 2026-10-09T13:40:50.702154+00:00
-- url     : https://prove2.me/submissions/f0c5a51c-c8bd-40f6-9906-1c263f223fb3

import Mathlib
import Definitions.Def_ChapterStoneUnitary
import Definitions.Def_ChapterStoneEvolution
import Definitions.Def_ChapterStoneGroup
import Definitions.Def_ChapterStoneResolvent
import Definitions.Def_ChapterSirkTrotterKato
open BookProof.ChapterStoneResolvent
open BookProof.ChapterStoneResolvent.UnboundedSelfAdjoint
open scoped InnerProductSpace
open Filter Topology NormedSpace

theorem solution {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]
    (T : UnboundedSelfAdjoint H) (t : ℝ) : T.approxU 0 t = 1 := by
  simp [approxU, yosidaGen, yosida]
