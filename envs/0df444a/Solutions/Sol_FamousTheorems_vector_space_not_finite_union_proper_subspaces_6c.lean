-- Prove2me | solution 1 for FamousTheorems.vector_space_not_finite_union_proper_subspaces_6c
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T11:02:01.824013+00:00
-- url     : https://prove2.me/submissions/af170457-43c7-4515-b211-8b965f3f9198

import Mathlib

theorem solution {k E : Type*} [DivisionRing k] [Infinite k] [AddCommGroup E] [Module k E] {s : Finset (Subspace k E)}
    (hs : ⊤ ∉ s) : ⋃ p ∈ s, (p : Set E) ≠ Set.univ :=
  Subspace.biUnion_ne_univ_of_top_notMem hs
