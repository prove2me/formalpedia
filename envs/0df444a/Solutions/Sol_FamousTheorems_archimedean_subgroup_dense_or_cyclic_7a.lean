-- Prove2me | solution 1 for FamousTheorems.archimedean_subgroup_dense_or_cyclic_7a
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T13:02:29.868966+00:00
-- url     : https://prove2.me/submissions/75417dd1-7504-415a-829e-7f3abd69dfa7

import Mathlib

theorem solution {G : Type*} [CommGroup G] [LinearOrder G] [IsOrderedMonoid G] [TopologicalSpace G] [OrderTopology G]
    [MulArchimedean G] (S : Subgroup G) : Dense (S : Set G) ∨ ∃ a : G, S = Subgroup.closure {a} :=
  S.dense_or_cyclic
