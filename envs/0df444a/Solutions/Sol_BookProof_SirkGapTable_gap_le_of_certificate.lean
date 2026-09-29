-- Prove2me | solution 1 for BookProof.SirkGapTable.gap_le_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:38:57.419073+00:00
-- url     : https://prove2.me/submissions/54db58a9-10bf-4cae-b93a-90bc40be36f0

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.gap_le_of_certificate
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hEven : thetaE - deltaE ≤ sectorGround T P 1)
    (hOdd : sectorGround T P (-1) ≤ thetaO + deltaO) :
    sectorGround T P (-1) - sectorGround T P 1 ≤ thetaO - thetaE + (deltaO + deltaE) := by
  linarith

#print axioms solution
