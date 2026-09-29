-- Prove2me | solution 1 for BlockCycleRotation.remSum_fib_consec
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:24:38.784432+00:00
-- url     : https://prove2.me/submissions/927d77c1-819a-48ef-901f-03a5a65a4744

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
import Mathlib


namespace BlockCycleRotation

@[simp]
theorem remSum_zero (n : ℕ) : remSum n 0 = 0 := by
  rw [remSum]; simp

/-- The defining recursion, in the form we actually use. -/
theorem remSum_of_pos {k : ℕ} (n : ℕ) (hk : k ≠ 0) :
    remSum n k = k + remSum k (n % k) := by
  rw [remSum]; simp [hk]

@[simp]
theorem cost_zero (n : ℕ) : cost n 0 = 0 := by
  rw [cost]; simp

@[simp]
theorem finalSeg_zero (n : ℕ) : finalSeg n 0 = n := by
  rw [finalSeg]; simp

/-- One Euclidean step on consecutive Fibonacci numbers.  (Stated from index `2`
upwards: at the very bottom `F₁ = F₂ = 1` and the pattern breaks.) -/
theorem fib_mod_fib (j : ℕ) : Nat.fib (j + 4) % Nat.fib (j + 3) = Nat.fib (j + 2) := by
  have hsplit : Nat.fib (j + 4) = Nat.fib (j + 2) + Nat.fib (j + 3) := Nat.fib_add_two
  have hlt : Nat.fib (j + 2) < Nat.fib (j + 3) := Nat.fib_lt_fib_succ (n := j + 2) (by omega)
  rw [hsplit, Nat.add_mod_right]
  exact Nat.mod_eq_of_lt hlt

end BlockCycleRotation

open BlockCycleRotation in
/-- Consecutive Fibonacci numbers: `remSum F_{m+1} F_m = F_{m+2} - 2` for `m ≥ 2`. -/
theorem solution : ∀ j : ℕ, remSum (Nat.fib (j + 3)) (Nat.fib (j + 2)) =
    Nat.fib (j + 4) - 2:= by
  intro j
  induction j with
  | zero =>
    have h2 : Nat.fib 2 = 1 := by decide
    have h3 : Nat.fib 3 = 2 := by decide
    have h4 : Nat.fib 4 = 3 := by decide
    norm_num [h2, h3, h4, remSum_of_pos (k := 1) 2 (by norm_num)]
  | succ J ih =>
    have hfib0 : Nat.fib (J + 3) ≠ 0 := (Nat.fib_pos.2 (by omega)).ne'
    have e1 : J + 1 + 2 = J + 3 := by omega
    have e2 : J + 1 + 3 = J + 4 := by omega
    have e3 : J + 1 + 4 = J + 5 := by omega
    rw [e1, e2, e3]
    rw [remSum_of_pos _ hfib0, fib_mod_fib J, ih]
    have hadd : Nat.fib (J + 5) = Nat.fib (J + 3) + Nat.fib (J + 4) := by
      have h : Nat.fib (J + 3 + 2) = Nat.fib (J + 3) + Nat.fib (J + 3 + 1) := Nat.fib_add_two
      have e4 : J + 3 + 2 = J + 5 := by omega
      have e5 : J + 3 + 1 = J + 4 := by omega
      rw [e4, e5] at h
      exact h
    have hpos : 2 ≤ Nat.fib (J + 4) := by
      have h : Nat.fib 3 ≤ Nat.fib (J + 4) := Nat.fib_mono (by omega)
      have h3 : Nat.fib 3 = 2 := by decide
      omega
    omega
