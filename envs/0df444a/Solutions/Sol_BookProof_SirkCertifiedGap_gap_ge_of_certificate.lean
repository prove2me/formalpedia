-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.gap_ge_of_certificate
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:38:58.527212+00:00
-- url     : https://prove2.me/submissions/4db998c8-3dc5-4af6-ab1b-302de8002fc6

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.gap_ge_of_certificate
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
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) :
    c.lower ≤ sectorGround T P (-1) - sectorGround T P 1 := by
  unfold GapCertificate.lower
  rw [hgap, hwidth]
  linarith

#print axioms solution
