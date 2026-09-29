-- Prove2me | solution 1 for FamousTheorems.stone_separation_theorem
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-24T01:56:24.590875+00:00
-- url     : https://prove2.me/submissions/a9d78cbf-dac8-41d8-8ff0-7846bace17e5

import Mathlib

theorem solution {𝕜 E : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜] [AddCommGroup E] [Module 𝕜 E] {s t : Set E}
    (hs : Convex 𝕜 s) (ht : Convex 𝕜 t) (hst : Disjoint s t) :
    ∃ C : Set E, Convex 𝕜 C ∧ Convex 𝕜 Cᶜ ∧ s ⊆ C ∧ t ⊆ Cᶜ :=
  exists_convex_convex_compl_subset hs ht hst
