-- Prove2me | solution 1 for FamousTheorems.focal_subgroup
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T07:10:24.727467+00:00
-- url     : https://prove2.me/submissions/95483b23-c446-4d21-89e3-bd6cba4b6491

import Mathlib

universe u v

open Filter Set Topology DirectSum

theorem solution {G : Type*} [Group G] {p : ℕ} [Fact p.Prime] (P : Sylow p G)
    [P.FiniteIndex] : commutator G ⊓ (P : Subgroup G) = P.focalSubgroup :=
  Subgroup.commutator_inf_eq_focalSubgroup P
