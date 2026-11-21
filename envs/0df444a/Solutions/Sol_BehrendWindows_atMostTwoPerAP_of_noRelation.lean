-- Prove2me | solution 1 for BehrendWindows.atMostTwoPerAP_of_noRelation
-- status  : ACCEPTED   (prove)
-- author  : @pitimespi
-- created : 2026-11-21T01:54:09.251302+00:00
-- url     : https://prove2.me/submissions/91e3e74f-3f50-4564-880b-36d05bc55d99

import Mathlib
import Definitions.Def_BehrendWindows_AtMostTwoPerAP
import Definitions.Def_BehrendWindows_NoRelation

open BehrendWindows

theorem solution {T : Finset ℤ} {L : ℕ}
    (h : NoRelation T L) : AtMostTwoPerAP T (L + 1) := by
  intro a d hd k₁ k₂ k₃ h12 h23 h3 ⟨m1, m2, m3⟩
  have hne : ∀ {x y : ℕ}, x < y → a + x * d ≠ a + y * d := by
    intro x y hxy e
    have : ((y : ℤ) - x) * d = 0 := by linear_combination -e
    rcases mul_eq_zero.1 this with h | h
    · omega
    · exact hd h
  refine h _ m1 _ m2 _ m3 (hne h12) (hne (h12.trans h23)) (hne h23)
    ((k₂ : ℤ) - k₁) ((k₃ : ℤ) - k₁) (by omega) (by omega) (by omega)
    (by rw [abs_le]; constructor <;> omega) (by rw [abs_le]; constructor <;> omega) ?_
  ring
