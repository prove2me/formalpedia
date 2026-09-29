-- Prove2me | solution 1 for BookProof.SirkCertifiedGap.certifiedGap_sound
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T08:12:19.428075+00:00
-- url     : https://prove2.me/submissions/5fbb1aec-01f9-4652-ac8d-ccec8369d635

-- Generated from ChapterSirkCertifiedGap.lean — theorem BookProof.SirkCertifiedGap.certifiedGap_sound
import Definitions.Def_ChapterSirkCertifiedGap
open BookProof.SirkCertifiedGap










noncomputable section


open scoped InnerProductSpace
open Finset Filter Topology
open BookProof.SirkFinitePrecision

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [FiniteDimensional ℂ E]

set_option autoImplicit false

theorem solution {T P : E →ₗ[ℂ] E} {thetaE thetaO deltaE deltaO : ℕ → ℝ} {m : ℕ}
    (hEven : sectorGround T P 1 ≤ thetaE m + deltaE m)
    (hOdd : thetaO m - deltaO m ≤ sectorGround T P (-1))
    (hpos : 0 < certifiedGap thetaE thetaO deltaE deltaO m) :
    certifiedGap thetaE thetaO deltaE deltaO m
        ≤ sectorGround T P (-1) - sectorGround T P 1
      ∧ sectorGround T P 1 < sectorGround T P (-1) := by
  unfold certifiedGap at hpos ⊢
  constructor <;> linarith

#print axioms solution
