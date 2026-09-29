-- Prove2me | solution 1 for BookProof.SirkGapTable.richardson_qym_g4
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:46.143766+00:00
-- url     : https://prove2.me/submissions/b33d909b-b4f5-4f58-84c1-28dcf51d07fe

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.richardson_qym_g4
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]














open Real

set_option autoImplicit false

theorem solution :
    richardson qymG4L3 qymG4L4 3 4 2 = 27999423 / 3500000 := by
  norm_num [richardson, qymG4L3, qymG4L4, Real.rpow_two]

#print axioms solution
