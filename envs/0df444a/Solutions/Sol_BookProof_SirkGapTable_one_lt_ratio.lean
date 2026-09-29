-- Prove2me | solution 1 for BookProof.SirkGapTable.one_lt_ratio
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:42.904365+00:00
-- url     : https://prove2.me/submissions/7b694516-046d-47e3-9ee5-6d7fce878ed6

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.one_lt_ratio
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]














open Real

set_option autoImplicit false

theorem solution {l1 l2 p : ℝ} (hl1 : 0 < l1) (hl : l1 < l2) (hp : 0 < p) :
    1 < (l2 / l1) ^ p := by
  apply Real.one_lt_rpow _ hp
  exact (one_lt_div hl1).2 hl

#print axioms solution
