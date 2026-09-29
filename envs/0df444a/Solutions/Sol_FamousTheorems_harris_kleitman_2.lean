-- Prove2me | solution 2 for FamousTheorems.harris_kleitman
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:50:47.034093+00:00
-- url     : https://prove2.me/submissions/10592f95-99b3-474a-badb-b6757dff3d89

import Mathlib

theorem solution {α : Type*} [DecidableEq α] [Fintype α] {𝒜 ℬ : Finset (Finset α)} (h𝒜 : IsLowerSet (𝒜 : Set (Finset α)))
    (hℬ : IsLowerSet (ℬ : Set (Finset α))) : 𝒜.card * ℬ.card ≤ 2 ^ Fintype.card α * (𝒜 ∩ ℬ).card :=
  h𝒜.le_card_inter_finset hℬ
