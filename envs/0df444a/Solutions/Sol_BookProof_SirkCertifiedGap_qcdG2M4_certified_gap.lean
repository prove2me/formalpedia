-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.qcdG2M4_certified_gap
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:09:45.363184+00:00
-- url     : https://prove2.me/submissions/e65a8739-3b81-4326-9f26-d9147409d272

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.qcdG2M4_certified_gap
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℝ}
    (hgap : thetaO - thetaE = 1.9875) (hwidth : deltaO + deltaE = 0.0555)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1)) :
    (1.932 : ℝ) ≤ sectorGround T P (-1) - sectorGround T P 1
      ∧ sectorGround T P 1 < sectorGround T P (-1) := by
  constructor <;> linarith

#print axioms solution
