-- Prove2me | solution 1 for BookProof.SirkGapTable.qcdG2M4_strongCoupling_consistent
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:44.522256+00:00
-- url     : https://prove2.me/submissions/9c57d29d-151a-4179-818c-88dbac52930e

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.qcdG2M4_strongCoupling_consistent
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false

theorem solution : qcdG2M4Row.strongCouplingConsistent := by
  norm_num [CouplingCertificate.strongCouplingConsistent,
    CouplingCertificate.lo, CouplingCertificate.hi, strongCoupling, qcdG2M4Row]

#print axioms solution
