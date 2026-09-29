-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.certified_parity_gap_pos
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:39:00.106981+00:00
-- url     : https://prove2.me/submissions/7a8bcfe3-405d-403a-b522-2f56f7136564

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certified_parity_gap_pos
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    (hsep : 0 < thetaO - thetaE - (deltaO + deltaE)) :
    sectorGround T P 1 < sectorGround T P (-1) := by
  linarith

#print axioms solution
