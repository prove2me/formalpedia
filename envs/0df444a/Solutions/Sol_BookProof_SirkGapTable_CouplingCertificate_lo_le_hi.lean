-- Prove2me | solution 1 for BookProof.SirkGapTable.CouplingCertificate.lo_le_hi
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:49.217234+00:00
-- url     : https://prove2.me/submissions/982962b4-c6f4-4d5a-8d02-a493c6e4a723

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.CouplingCertificate.lo_le_hi
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable
open BookProof.SirkGapTable.CouplingCertificate









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false

theorem solution (c : CouplingCertificate) : c.lo ≤ c.hi := by
  unfold CouplingCertificate.lo CouplingCertificate.hi
  linarith [c.width_nonneg]

#print axioms solution
