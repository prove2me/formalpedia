-- Prove2me | solution 1 for BookProof.SirkGapTable.strongCoupling_lt
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:43.694768+00:00
-- url     : https://prove2.me/submissions/12ae9b5b-dd1e-43e1-870c-81e6d5e983f3

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.strongCoupling_lt
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false

theorem solution {g₁ g₂ : ℝ} (h0 : 0 ≤ g₁) (h : g₁ < g₂) :
    strongCoupling g₁ < strongCoupling g₂ := by
  unfold strongCoupling
  nlinarith

#print axioms solution
