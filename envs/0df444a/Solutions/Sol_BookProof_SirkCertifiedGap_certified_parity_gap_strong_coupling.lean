-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.certified_parity_gap_strong_coupling
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T07:38:56.385512+00:00
-- url     : https://prove2.me/submissions/7fc5d6e2-c64f-4577-befc-3babfdd92f43

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certified_parity_gap_strong_coupling
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E}
    {thetaE thetaO deltaE deltaO g corr : ℝ}
    (hform : thetaO - thetaE = g ^ 2 / 2 + corr)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) :
    g ^ 2 / 2 + corr - (deltaO + deltaE)
      ≤ sectorGround T P (-1) - sectorGround T P 1 := by
  linarith

#print axioms solution
