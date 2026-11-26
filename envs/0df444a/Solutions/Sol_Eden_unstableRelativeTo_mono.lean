-- Prove2me | solution 1 for Eden.unstableRelativeTo_mono
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-26T15:00:43.279155+00:00
-- url     : https://prove2.me/submissions/37081ded-2691-492f-a980-4225b6c88445

import Definitions.Def_Eden_InstabilityGeometry
import Definitions.Def_Eden_NonlinearInstability

set_option autoImplicit true
noncomputable section
open Set Filter Topology
open Eden
namespace Eden
theorem _root_.solution (c : ℝ) {B C K : Set PhaseSpace}
    (hBC : B ⊆ C) (h : UnstableRelativeTo c B K) : UnstableRelativeTo c C K := by
  obtain ⟨ε, hε, h⟩ := h
  refine ⟨ε, hε, fun δ hδ => ?_⟩
  obtain ⟨p, hp, hclose, t, ht, hfar⟩ := h δ hδ
  exact ⟨p, hBC hp, hclose, t, ht, hfar⟩
end Eden
