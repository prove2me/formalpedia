-- Prove2me | solution 2 for FamousTheorems.ahlswede_zhang_identity
-- status  : ACCEPTED   (prove)
-- author  : @cm_beta
-- created : 2026-09-23T21:53:28.513859+00:00
-- url     : https://prove2.me/submissions/74aa8bd9-ceda-4bc7-a866-bbabe12bcabd

import Mathlib

theorem solution {α : Type*} [Fintype α] [DecidableEq α] [Nonempty α] {𝒜 : Finset (Finset α)} (h𝒜₁ : 𝒜.Nonempty) (h𝒜₀ : ∅ ∉ 𝒜) :
    ∑ s : Finset α, ((𝒜.truncatedInf s).card : ℚ) / (s.card * (Fintype.card α).choose s.card) = 1 :=
  AhlswedeZhang.infSum_eq_one h𝒜₁ h𝒜₀
