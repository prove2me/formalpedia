-- Prove2me | solution 1 for FamousTheorems.first_isomorphism
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T06:56:21.905558+00:00
-- url     : https://prove2.me/submissions/986f5f03-7701-4487-b0ad-258058011898

import Mathlib

open Filter Set Topology

theorem solution {G : Type*} [Group G] {H : Type*} [Group H] (φ : G →* H) :
    Nonempty (G ⧸ φ.ker ≃* φ.range) := ⟨QuotientGroup.quotientKerEquivRange φ⟩
