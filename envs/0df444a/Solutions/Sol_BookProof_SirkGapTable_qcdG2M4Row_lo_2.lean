-- Prove2me | solution 2 for BookProof.SirkGapTable.qcdG2M4Row_lo
-- status  : ACCEPTED   (prove)
-- author  : @leonardopedro
-- created : 2026-09-29T20:13:56.499625+00:00
-- url     : https://prove2.me/submissions/9493d482-abc2-42de-97a1-24d6c9d5de16

-- Generated from ChapterSirkGapTable.lean — solution of BookProof.SirkGapTable.qcdG2M4Row_lo
import Mathlib
import Definitions.Def_ChapterSirkGapTable
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkGapTable










noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option maxHeartbeats 1000000 in
theorem solution : qcdG2M4Row.lo = 1.932 ∧ qcdG2M4Row.hi = 2.043 := by

  constructor <;> norm_num [CouplingCertificate.lo, CouplingCertificate.hi, qcdG2M4Row]
