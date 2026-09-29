-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.certified_parity_gap
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:38:59.329543+00:00
-- url     : https://prove2.me/submissions/94524959-1de4-44c1-9cad-e24cbd32ced3

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certified_parity_gap
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
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) :
    thetaO - thetaE - (deltaO + deltaE) ≤ sectorGround T P (-1) - sectorGround T P 1 := by
  linarith

#print axioms solution
