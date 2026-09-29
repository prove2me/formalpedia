-- Prove2me | solution 1 for BookProof.FockOneParticleGap.one_particle_edge_ge_of_parity_certificate
-- status  : ACCEPTED   (prove)
-- author  : @wamlart
-- created : 2026-09-12T09:33:41.378354+00:00
-- url     : https://prove2.me/submissions/2339ff4a-f261-4cfc-aed8-7cba76e8ba9c

import Definitions.Def_ChapterFockOneParticleGap
-- Adapted from Leonardo Pedro, timepiece commit 61595bc (Apache-2.0).
noncomputable section
set_option autoImplicit false
set_option linter.unusedSectionVars false

-- Generated from ChapterFockOneParticleGap.lean — theorem BookProof.FockOneParticleGap.one_particle_edge_ge_of_parity_certificate
open BookProof.FockOneParticleGap












noncomputable section


open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology
















































variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open BookProof.SirkCertifiedGap
open BookProof.SirkCertifiedGap

theorem solution {T P : E →ₗ[ℂ] E} (c : GapCertificate)
    {thetaE thetaO deltaE deltaO lam : ℝ}
    (hgap : c.gap = thetaO - thetaE) (hwidth : c.width = deltaO + deltaE)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    (hvac : sectorGround T P 1 = 0) (hone : sectorGround T P (-1) = lam) :
    c.lower ≤ lam := by
  unfold GapCertificate.lower
  rw [hgap, hwidth]
  rw [hvac] at hEven
  rw [hone] at hOdd
  linarith

#print axioms solution
