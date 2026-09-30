-- Prove2me | solution 2 for BookProof.SirkGapTable.qcdG2M4_strongCoupling_consistent
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T20:19:32.686301+00:00
-- url     : https://prove2.me/submissions/59a5adc8-e7b2-4017-86c8-e182f73f66e4

-- Generated from ChapterSirkGapTable.lean — solution of BookProof.SirkGapTable.qcdG2M4_strongCoupling_consistent
import Mathlib
import Definitions.Def_ChapterSirkGapTable
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkGapTable










noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution : qcdG2M4Row.strongCouplingConsistent := by

  constructor <;>
    norm_num [CouplingCertificate.lo, CouplingCertificate.hi, qcdG2M4Row, strongCoupling]
