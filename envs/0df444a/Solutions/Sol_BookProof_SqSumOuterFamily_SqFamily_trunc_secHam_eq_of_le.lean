-- Prove2me | solution 1 for BookProof.SqSumOuterFamily.SqFamily.trunc_secHam_eq_of_le
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-11-08T21:10:19.437583+00:00
-- url     : https://prove2.me/submissions/55176db5-05f2-487b-9ca9-0713da99ac4d

-- Generated from ChapterSqSumOuterSingleTime.lean — solution of BookProof.SqSumOuterFamily.SqFamily.trunc_secHam_eq_of_le
import Mathlib
import Definitions.Def_ChapterSqSumOuterSingleTime
import Definitions.Def_ChapterFarisLavine
import Definitions.Def_ChapterEsaClosureCore
import Definitions.Def_ChapterStoneBridge
import Definitions.Def_ChapterSirkTrotterKato
import Definitions.Def_ChapterComplexShiftCore
import Definitions.Def_ChapterSirkSingleTimeShift
import Definitions.Def_ChapterQgTimeIndependentFlowPromoted
import Definitions.Def_ChapterQgTruncationResolvent
import Definitions.Def_ChapterDirectSumEsa
import Definitions.Def_ChapterHermiteProductCore
import Definitions.Def_ChapterQgOuterFockEsa
import Definitions.Def_ChapterSqSumOuterFamily
open BookProof.SqSumOuterFamily
open BookProof.SqSumOuterFamily.SqFamily




open Filter Topology
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.ChapterSirkTrotterKato
open BookProof.HashimotoShiftInvert BookProof.SirkSingleTime
open BookProof.QgTimeIndependent BookProof.QgTruncationResolvent
open BookProof.DirectSumEsa BookProof.HermiteProductCore
open BookProof.HermiteProductCore
open BookProof.QgOuterFock

noncomputable section

set_option maxHeartbeats 1000000 in
theorem solution (F : SqFamily) {N n : ℕ} (h : n ≤ N) :
    (F.trunc N).secHam n = F.secHam n := by

  have hvv : (F.trunc N).vv n = F.vv n := by
    funext r I
    simp [trunc, h]
  rw [secHam, secHam, hvv]
  rfl
