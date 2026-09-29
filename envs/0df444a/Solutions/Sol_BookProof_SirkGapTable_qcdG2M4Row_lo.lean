-- Prove2me | solution 1 for BookProof.SirkGapTable.qcdG2M4Row_lo
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:39.93905+00:00
-- url     : https://prove2.me/submissions/0cd1cc58-915b-4e26-a807-2879f79e76af

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.qcdG2M4Row_lo
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false

theorem solution : qcdG2M4Row.lo = 1.932 ∧ qcdG2M4Row.hi = 2.043 := by
  norm_num [CouplingCertificate.lo, CouplingCertificate.hi, qcdG2M4Row]

#print axioms solution
