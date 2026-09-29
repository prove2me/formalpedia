-- Prove2me | solution 1 for FamousTheorems.ahlswede_zhang_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:51:06.456816+00:00
-- url     : https://prove2.me/submissions/93c72792-fd55-46e0-a06d-70ae457b369f

import Mathlib

theorem solution {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {𝒜 : Finset (Finset α)} (h𝒜₁ : 𝒜.Nonempty) (h𝒜₀ : ∅ ∉ 𝒜) :
    ∑ s : Finset α, ((𝒜.truncatedInf s).card : ℚ) / (s.card * (Fintype.card α).choose s.card) = 1 :=
  AhlswedeZhang.infSum_eq_one h𝒜₁ h𝒜₀
