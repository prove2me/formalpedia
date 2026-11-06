-- Prove2me | solution 1 for BookProof.FarisLavineOnly.secHam_esa_fl
-- status  : ACCEPTED   (prove)
-- author  : @nonlocally
-- created : 2026-11-05T18:54:15.671664+00:00
-- url     : https://prove2.me/submissions/f681ec52-f985-461e-803f-2403d4cc89fd

import Theorems.Thm_BookProof_FarisLavineOnly_sqSumOp_esa_farisLavine
import Definitions.Def_ChapterSqSumOuterFamily

open BookProof.FarisLavine
open BookProof.HermiteProductCore BookProof.QgOuterFockCoreFL
open BookProof.SqSumOuterFamily

noncomputable section

theorem solution (F : SqFamily) (n : ℕ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := F.dim n)) (F.secHam n) := by
  exact BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine (F.kap n) (F.vv n)
