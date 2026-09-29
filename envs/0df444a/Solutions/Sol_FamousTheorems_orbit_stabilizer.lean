-- Prove2me | solution 1 for FamousTheorems.orbit_stabilizer
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T06:56:30.203249+00:00
-- url     : https://prove2.me/submissions/7835e3d9-43d3-4913-a82e-711c0c0b81f3

import Mathlib

open Filter Set Topology

theorem solution {G : Type*} [Group G] {X : Type*} [MulAction G X] (b : X) :
    Nonempty (MulAction.orbit G b ≃ G ⧸ MulAction.stabilizer G b) :=
  ⟨MulAction.orbitEquivQuotientStabilizer G b⟩
