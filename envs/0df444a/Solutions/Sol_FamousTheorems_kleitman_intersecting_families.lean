-- Prove2me | solution 1 for FamousTheorems.kleitman_intersecting_families
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:52:57.72317+00:00
-- url     : https://prove2.me/submissions/ebf0b06d-a57c-4189-83eb-b0b9148292da

import Mathlib

theorem solution {ι α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] (s : Finset ι) (f : ι → Finset (Finset α))
    (hf : ∀ i ∈ s, (f i : Set (Finset α)).Intersecting) :
    (s.biUnion f).card ≤ 2 ^ Fintype.card α - 2 ^ (Fintype.card α - s.card) :=
  Finset.card_biUnion_le_of_intersecting s f hf
