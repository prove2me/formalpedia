-- Prove2me | solution 1 for BehrendWindows.atMostTwoPerAP_mono
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:54:08.660362+00:00
-- url     : https://prove2.me/submissions/6e1ea734-7e1b-43e7-8377-87d8b37521e9

import Mathlib
import Definitions.Def_BehrendWindows_AtMostTwoPerAP

open BehrendWindows

theorem solution {T T' : Finset ℤ} {m m' : ℕ} (c : ℤ)
    (hT : T' ⊆ T.image (· + c)) (hm : m' ≤ m) (h : AtMostTwoPerAP T m) :
    AtMostTwoPerAP T' m' := by
  intro a d hd k₁ k₂ k₃ h1 h2 h3 ⟨m1, m2, m3⟩
  have g : ∀ k : ℕ, a + k * d ∈ T' → a - c + k * d ∈ T := by
    intro k hk
    obtain ⟨t, ht, e⟩ := Finset.mem_image.1 (hT hk)
    have : a - c + k * d = t := by linarith
    simpa [this]
  exact h (a - c) d hd k₁ k₂ k₃ h1 h2 (by omega) ⟨g _ m1, g _ m2, g _ m3⟩
