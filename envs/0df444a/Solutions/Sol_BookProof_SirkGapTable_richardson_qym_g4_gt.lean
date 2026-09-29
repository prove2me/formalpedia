-- Prove2me | solution 1 for BookProof.SirkGapTable.richardson_qym_g4_gt
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:47.64439+00:00
-- url     : https://prove2.me/submissions/4c377cd6-bc50-4dc6-82ea-0f5f94b1ae0d

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.richardson_qym_g4_gt
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]














open Real

set_option autoImplicit false

theorem solution : qymG4L4 < richardson qymG4L3 qymG4L4 3 4 2 := by
  norm_num [richardson, qymG4L3, qymG4L4, Real.rpow_two]

#print axioms solution
