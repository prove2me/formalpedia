-- Prove2me | solution 1 for FamousTheorems.t0_embeds_in_sierpinski_power_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:53:51.192974+00:00
-- url     : https://prove2.me/submissions/f4a7c194-dcaf-4435-963e-a0d223d9d539

import Mathlib

universe u

theorem solution (X : Type u) [TopologicalSpace X] [T0Space X] :
    ∃ (ι : Type u) (f : X → (ι → Prop)), Topology.IsEmbedding f :=
  ⟨_, _, TopologicalSpace.productOfMemOpens_isEmbedding X⟩
