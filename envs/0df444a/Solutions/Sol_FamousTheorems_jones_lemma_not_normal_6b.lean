-- Prove2me | solution 1 for FamousTheorems.jones_lemma_not_normal_6b
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T10:56:30.41425+00:00
-- url     : https://prove2.me/submissions/b53485e7-a5bd-48d8-b03d-cd39f76f9219

import Mathlib

theorem solution {X : Type*} [TopologicalSpace X] [TopologicalSpace.SeparableSpace X] {s : Set X} (hs : IsClosed s)
    [DiscreteTopology s] (hc : Cardinal.continuum ≤ Cardinal.mk s) : ¬NormalSpace X :=
  hs.not_normal_of_continuum_le_mk hc
