-- Prove2me | solution 1 for FamousTheorems.harris_kleitman
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:49:27.661444+00:00
-- url     : https://prove2.me/submissions/b8060466-3526-44a3-b317-760fadcb5577

import Mathlib

theorem solution {α : Type*} [DecidableEq α] [Fintype α] {𝒜 ℬ : Finset (Finset α)} (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) : 𝒜.card * ℬ.card ≤ 2 ^ Fintype.card α * (𝒜 ∩ ℬ).card :=
  h𝒜.le_card_inter_finset hℬ
