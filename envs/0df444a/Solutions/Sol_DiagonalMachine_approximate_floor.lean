-- Prove2me | solution 1 for DiagonalMachine.approximate_floor
-- status  : ACCEPTED   (prove)
-- author  : @bueno_ricardo
-- created : 2026-11-15T19:02:40.859974+00:00
-- url     : https://prove2.me/submissions/75861bd8-f081-44d2-99e9-52ce08299728

import Mathlib
import Theorems.Thm_DiagonalMachine_depth_persists
open MeasureTheory Set
open DiagonalMachine

theorem solution (a : ℕ → ℝ)
    (hstep : ∀ n, a n < 0 → a (n+1) ≤ a n)
    (hfloor : ∀ K, ∀ ε : ℝ, 0 < ε → ∃ n, K ≤ n ∧ -ε ≤ a n) :
    ∀ k, 0 ≤ a k := by
  intro k
  by_contra h
  have hk : a k < 0 := lt_of_not_ge h
  obtain ⟨n, hkn, hn⟩ := hfloor k (-a k/2) (by linarith)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hkn
  have hp := depth_persists a hstep k hk j
  linarith
