-- Prove2me | solution 1 for DeletionCode.TwoEditWindows.exists_clean_block_among_three
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-19T06:16:50.441873+00:00
-- url     : https://prove2.me/submissions/8997cf6a-cf7a-4af1-8b1a-5eba3cf3f21a

import Mathlib.Data.Nat.Basic
import Lean.Elab.Tactic.Omega
import Definitions.Def_DeletionCode_TwoEditWindows
import Theorems.Thm_DeletionCode_TwoEditWindows_avoids_later_of_not_avoids

set_option autoImplicit true
open DeletionCode DeletionCode.TwoEditWindows
namespace DeletionCode.TwoEditWindows
theorem _root_.solution (k a b p q : ℕ) :
    ∃ s : ℕ, (s = 0 ∨ s = k + 1 ∨ s = 2 * (k + 1)) ∧
      s + k ≤ 3 * k + 2 ∧
      (a + s + k ≤ p ∨ p < a + s) ∧
      (b + s + k ≤ q ∨ q < b + s) := by
  by_cases ha0 : Avoids k a p
  · by_cases hb0 : Avoids k b q
    · refine ⟨0, Or.inl rfl, by omega, ?_, ?_⟩
      · simpa only [Avoids, Nat.add_zero] using ha0
      · simpa only [Avoids, Nat.add_zero] using hb0
    · have hb1 : Avoids k (b + (k + 1)) q :=
        avoids_later_of_not_avoids (by omega) hb0
      have hb2 : Avoids k (b + 2 * (k + 1)) q :=
        avoids_later_of_not_avoids (by omega) hb0
      by_cases ha1 : Avoids k (a + (k + 1)) p
      · exact ⟨k + 1, Or.inr (Or.inl rfl), by omega, ha1, hb1⟩
      · have ha2 : Avoids k (a + 2 * (k + 1)) p :=
          avoids_later_of_not_avoids (by omega) ha1
        exact ⟨2 * (k + 1), Or.inr (Or.inr rfl), by omega, ha2, hb2⟩
  · have ha1 : Avoids k (a + (k + 1)) p :=
      avoids_later_of_not_avoids (by omega) ha0
    have ha2 : Avoids k (a + 2 * (k + 1)) p :=
      avoids_later_of_not_avoids (by omega) ha0
    by_cases hb1 : Avoids k (b + (k + 1)) q
    · exact ⟨k + 1, Or.inr (Or.inl rfl), by omega, ha1, hb1⟩
    · have hb2 : Avoids k (b + 2 * (k + 1)) q :=
        avoids_later_of_not_avoids (by omega) hb1
      exact ⟨2 * (k + 1), Or.inr (Or.inr rfl), by omega, ha2, hb2⟩
end DeletionCode.TwoEditWindows
