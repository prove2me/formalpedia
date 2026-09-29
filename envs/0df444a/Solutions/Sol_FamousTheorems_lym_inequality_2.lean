-- Prove2me | solution 2 for FamousTheorems.lym_inequality
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:53:28.963971+00:00
-- url     : https://prove2.me/submissions/99140180-1469-4196-abb6-287cd9d6b350

import Mathlib

theorem solution {α : Type*} [Fintype α] {𝒜 : Finset (Finset α)} (h𝒜 : IsAntichain (· ⊆ ·) (𝒜 : Set (Finset α))) :
    ∑ r ∈ Finset.range (Fintype.card α + 1), ((𝒜.slice r).card / (Fintype.card α).choose r : ℚ) ≤ 1 :=
  Finset.lubell_yamamoto_meshalkin_inequality_sum_card_div_choose h𝒜
