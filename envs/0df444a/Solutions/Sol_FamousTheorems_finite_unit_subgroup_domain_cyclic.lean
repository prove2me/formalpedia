-- Prove2me | solution 1 for FamousTheorems.finite_unit_subgroup_domain_cyclic
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:06:23.054438+00:00
-- url     : https://prove2.me/submissions/fb902d25-093e-47a0-b404-f4211a32aa1e

import Mathlib

theorem solution {R : Type*} [CommRing R] [IsDomain R] (S : Subgroup Rˣ) [Finite S] : IsCyclic S :=
  isCyclic_subgroup_units S
