-- Prove2me | solution 1 for BookProof.SirkGapTable.strongCoupling_mem_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:39:01.859781+00:00
-- url     : https://prove2.me/submissions/44081687-ceb9-46e6-bc19-3841008634f8

-- Generated from ChapterSirkGapTable.lean — theorem BookProof.SirkGapTable.strongCoupling_mem_of_certificate
import Definitions.Def_ChapterSirkGapTable
open BookProof.SirkGapTable









noncomputable section


open BookProof.SirkCertifiedGap



variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]










variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

set_option autoImplicit false

theorem solution {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℂ E] {T P : E →ₗ[ℂ] E} (c : CouplingCertificate)
    {thetaE thetaO deltaE deltaO : ℝ}
    (hgap : c.gap = thetaO - thetaE) (hwidth : c.width = deltaO + deltaE)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    (hcons : c.strongCouplingConsistent) :
    c.lo ≤ sectorGround T P (-1) - sectorGround T P 1 ∧ c.lo ≤ strongCoupling c.g := by
  constructor
  · unfold CouplingCertificate.lo
    rw [hgap, hwidth]
    linarith
  · exact hcons.1

#print axioms solution
