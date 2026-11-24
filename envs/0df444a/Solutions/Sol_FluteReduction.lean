-- Prove2me | solution 1 for FluteReduction
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-24T10:10:19.573853+00:00
-- url     : https://prove2.me/submissions/dabd233f-099d-48f8-89bf-e13aacc4a461

import Definitions.Def_FriezePatterns_chapter1
import Definitions.Def_FriezePatterns_chapter2

set_option autoImplicit true

theorem _root_.solution (n : ℕ)(f : flute n) : ((f.a 1 =1) ∨ (f.a (n-2) = 1)) ∨ (∃ i ≤ n-3, f.a (i+1) = f.a i + f.a (i+2)) := by
  by_contra! H
  rcases H with ⟨⟨h₁, h₂⟩, h₃⟩
  have ha₁ : (↑(f.a 1):ℤ) - f.a 0 > 0 := by
    have := f.pos 1
    have := f.hd
    omega
  have ha₂ : (↑(f.a (n-1)):ℤ) - f.a (n-2) < 0 := by
    have := f.pos (n-2)
    have := f.period 0
    simp [f.hd] at this
    omega
  have key : ∀ i ≤ n-3, (↑(f.a i):ℤ) + f.a (i+2) ≥ (f.a (i+1))*2 := by
    intro i hi
    rcases f.div i with ⟨k, hk⟩
    match k with
    | 0 =>
      simp at hk
      have := f.pos i
      omega
    | 1 =>
      specialize h₃ i hi
      omega
    | k+2 =>
      nlinarith
  have key₂ : ∀ i ≤ n-3, (↑ (f.a (i+2)) : ℤ) - f.a (i+1) ≥ f.a 1 - f.a 0 := by
    intro i hi
    induction' i with i ih
    specialize key 0 hi
    linarith
    specialize key (i+1) hi
    specialize ih (by omega)
    linarith
  have key₃ : f.a (n-1) = 1 := by
    have := f.period 0
    simp [f.hd] at this
    rw [←this]
  match n with -- n ≤ 2 contradicts with h₁ and h₂
  | 0 => linarith
  | 1 => linarith
  | 2 => linarith
  | n+3 =>
    simp at *
    specialize key₂ n (by omega)
    linarith
