-- Prove2me | solution 1 for BookProof.SirkGapTable.certified_gap_mem_interval
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:41:49.519568+00:00
-- url     : https://prove2.me/submissions/905c860b-479b-432c-bfb5-942ed7c1d7a6

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.certified_gap_mem_interval
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hEvenHi : sectorGround T P 1 ≤ thetaE + deltaE)
    (hEvenLo : thetaE - deltaE ≤ sectorGround T P 1)
    (hOddLo : thetaO - deltaO ≤ sectorGround T P (-1))
    (hOddHi : sectorGround T P (-1) ≤ thetaO + deltaO) :
    sectorGround T P (-1) - sectorGround T P 1 ∈
      Set.Icc (thetaO - thetaE - (deltaO + deltaE)) (thetaO - thetaE + (deltaO + deltaE)) := by
  constructor <;> linarith

#print axioms solution
