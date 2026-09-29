-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.gap_pos_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:12:18.463513+00:00
-- url     : https://prove2.me/submissions/98fe18cf-979b-4e90-b14c-f5f5abd40111

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.gap_pos_of_certificate
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E} (c : GapCertificate)
    {thetaE thetaO deltaE deltaO : ℝ}
    (hgap : c.gap = thetaO - thetaE) (hwidth : c.width = deltaO + deltaE)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    (hpos : 0 < c.lower) :
    sectorGround T P 1 < sectorGround T P (-1) := by
  unfold GapCertificate.lower at hpos
  rw [hgap, hwidth] at hpos
  linarith

#print axioms solution
