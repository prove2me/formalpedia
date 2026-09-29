-- Prove2me | solution 1 for BlockCycleRotation.remSum_fib
-- status  : ACCEPTED   (prove)
-- author  : @dbenbenn
-- created : 2026-09-05T10:24:38.892361+00:00
-- url     : https://prove2.me/submissions/da9993cf-8b5c-4c5f-9e0e-d746e7afc66b

import Definitions.Def_BlockCycleRotation_Algorithm
import Definitions.Def_BlockCycleRotation_Euclid
import Theorems.Thm_BlockCycleRotation_remSum_fib_consec
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

end BlockCycleRotation

open BlockCycleRotation in
/-- The paper's `n = F_{m+2}`, `k = F_m` case: `remSum = F_{m+2} - 2`. -/
theorem solution (j : ℕ) :
    remSum (Nat.fib (j + 4)) (Nat.fib (j + 2)) = Nat.fib (j + 4) - 2:= by
  have hfib0 : Nat.fib (j + 2) ≠ 0 := (Nat.fib_pos.2 (by omega)).ne'
  rcases Nat.eq_zero_or_pos j with hj | hj
  · -- `j = 0`: here `F₂ = 1` divides `F₄ = 3` and the recursion stops at once.
    subst hj
    have h2 : Nat.fib 2 = 1 := by decide
    have h4 : Nat.fib 4 = 3 := by decide
    norm_num [h2, h4, remSum_of_pos (k := 1) 3 (by norm_num)]
  · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
    have e2 : i + 1 + 2 = i + 3 := by omega
    have e4 : i + 1 + 4 = i + 5 := by omega
    rw [e2, e4]
    have hfib0' : Nat.fib (i + 3) ≠ 0 := (Nat.fib_pos.2 (by omega)).ne'
    have hsplit : Nat.fib (i + 5) = Nat.fib (i + 2) + 2 * Nat.fib (i + 3) := by
      have h1 : Nat.fib (i + 3 + 2) = Nat.fib (i + 3) + Nat.fib (i + 3 + 1) := Nat.fib_add_two
      have h2 : Nat.fib (i + 2 + 2) = Nat.fib (i + 2) + Nat.fib (i + 2 + 1) := Nat.fib_add_two
      have a1 : i + 3 + 2 = i + 5 := by omega
      have a2 : i + 3 + 1 = i + 4 := by omega
      have a3 : i + 2 + 2 = i + 4 := by omega
      have a4 : i + 2 + 1 = i + 3 := by omega
      rw [a1, a2] at h1
      rw [a3, a4] at h2
      omega
    have hlt : Nat.fib (i + 2) < Nat.fib (i + 3) := Nat.fib_lt_fib_succ (n := i + 2) (by omega)
    have hmod : Nat.fib (i + 5) % Nat.fib (i + 3) = Nat.fib (i + 2) := by
      rw [hsplit, Nat.mul_comm 2 (Nat.fib (i + 3)), Nat.add_mul_mod_self_left]
      exact Nat.mod_eq_of_lt hlt
    have hprev : remSum (Nat.fib (i + 3)) (Nat.fib (i + 2)) = Nat.fib (i + 4) - 2 :=
      remSum_fib_consec i
    have hpos : 2 ≤ Nat.fib (i + 4) := by
      have h : Nat.fib 3 ≤ Nat.fib (i + 4) := Nat.fib_mono (by omega)
      have h3 : Nat.fib 3 = 2 := by decide
      omega
    have hadd : Nat.fib (i + 5) = Nat.fib (i + 3) + Nat.fib (i + 4) := by
      have h : Nat.fib (i + 3 + 2) = Nat.fib (i + 3) + Nat.fib (i + 3 + 1) := Nat.fib_add_two
      have a1 : i + 3 + 2 = i + 5 := by omega
      have a2 : i + 3 + 1 = i + 4 := by omega
      rw [a1, a2] at h
      exact h
    rw [remSum_of_pos _ hfib0', hmod, hprev]
    omega
