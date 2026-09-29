-- Prove2me | solution 2 for FamousTheorems.kleitman_intersecting_families
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:54:04.903908+00:00
-- url     : https://prove2.me/submissions/e1dbac86-bcb6-4205-9662-2737a76f0801

import Mathlib

theorem solution {ι α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (s : Finset ι) (f : ι → Finset (Finset α))
    (hf : ∀ i ∈ s, (f i : Set (Finset α)).Intersecting) :
    (s.biUnion f).card ≤ 2 ^ Fintype.card α - 2 ^ (Fintype.card α - s.card) :=
  Finset.card_biUnion_le_of_intersecting s f hf
