-- Prove2me | solution 1 for FamousTheorems.all_card_le_biunion_card_iff_exists_injective
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-22T13:01:31.906809+00:00
-- url     : https://prove2.me/submissions/3677c88d-f6d6-4982-a0da-5d5cdddd87c7

import Mathlib

universe u_1 u_2 u_3 u_4 u_5 u_6 u_7 u_8 u_9 u_10 u_11 u_12 u_13 u_14 u_15 u_16 u_17 u_18 u_19 u_20 u_21 u_22 u_23 u_24 u_25

open Filter Set Topology DirectSum

theorem solution :
    ∀ {ι : Type u_1} {α : Type u_2} [inst : DecidableEq α] 
    (t : ι → Finset α), (∀ (s : Finset ι), s.card ≤ (s.biUnion t).card) ↔ ∃ f, Function.Injective f ∧ ∀ (x : ι), f x ∈ t x :=
  @_root_.Finset.all_card_le_biUnion_card_iff_exists_injective
