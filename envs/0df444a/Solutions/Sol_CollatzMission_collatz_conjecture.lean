-- Prove2me | solution 1 for CollatzMission.collatz_conjecture
-- status  : SKETCH_ACCEPTED   (prove)
-- author  : @mysticflounder
-- created : 2026-09-08T04:53:52.515543+00:00
-- url     : https://prove2.me/submissions/52bba91d-87a1-4cd7-a5a8-80dac036c8e6
-- note    : a sketch -- it imports a theorem that is still Open,
--           so it depends on `sorryAx` until that child is proved.

import Theorems.Thm_collatz_descent
import Theorems.Thm_collatz_iterate_pos

theorem solution (n : ℕ) (hn : 0 < n) : ∃ m : ℕ, collatzStep^[m] n = 1 := by
  revert hn
  induction n using Nat.strong_induction_on with
  | _ n ih =>
      intro hn
      by_cases h1 : n = 1
      · exact ⟨0, by simp [h1]⟩
      · have hlt1 : 1 < n := by omega
        obtain ⟨m, hlt⟩ := collatz_descent n hlt1
        obtain ⟨k, hk⟩ := ih _ hlt (collatz_iterate_pos m n hn)
        exact ⟨k + m, by rw [Function.iterate_add_apply]; exact hk⟩
