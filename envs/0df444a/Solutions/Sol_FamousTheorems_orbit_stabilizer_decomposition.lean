-- Prove2me | solution 1 for FamousTheorems.orbit_stabilizer_decomposition
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:27:45.379179+00:00
-- url     : https://prove2.me/submissions/3f4b324e-0106-40f9-99e7-0feb16bfa170

import Mathlib

theorem solution (G X : Type*) [Group G] [MulAction G X] :
    Nonempty (X ≃ Σ ω : Quotient (MulAction.orbitRel G X), G ⧸ MulAction.stabilizer G ω.out) :=
  ⟨MulAction.selfEquivSigmaOrbitsQuotientStabilizer G X⟩
