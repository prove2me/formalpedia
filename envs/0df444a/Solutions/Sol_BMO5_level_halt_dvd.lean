-- Prove2me | solution 1 for BMO5.level_halt_dvd
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T16:41:07.600547+00:00
-- url     : https://prove2.me/submissions/60ac7ba4-b641-462e-bc4d-54226a332885

import Mathlib

namespace BMO5Sol

theorem conj (i : ℕ) : ∀ k b : ℕ,
    2 * (fun x => 3 * x + i + 5)^[k] b + i + 5 = 3 ^ k * (2 * b + i + 5) := by
  intro k
  induction k with
  | zero => intro b; simp
  | succ k ih =>
    intro b
    have hb := ih b
    simp only [Function.iterate_succ_apply']
    generalize (fun x => 3 * x + i + 5)^[k] b = X at hb ⊢
    rw [pow_succ, show 3 ^ k * 3 * (2 * b + i + 5) = 3 * (3 ^ k * (2 * b + i + 5)) by ring, ← hb]
    ring

theorem dvd (i b k : ℕ) (h : (fun x => 3 * x + i + 5)^[k] b = 10 * 2 ^ i - 2) :
    3 ^ k ∣ 20 * 2 ^ i + i + 1 := by
  have e := conj i k b
  rw [h] at e
  have h2 : 20 * 2 ^ i + i + 1 = 3 ^ k * (2 * b + i + 5) := by
    have hp : 1 ≤ 2 ^ i := Nat.one_le_two_pow
    generalize 2 ^ i = P at e hp ⊢
    generalize 3 ^ k * (2 * b + i + 5) = Q at e ⊢
    omega
  exact ⟨_, h2⟩

end BMO5Sol

theorem solution (i b k : ℕ)
    (h : (fun x => 3 * x + i + 5)^[k] b = 10 * 2 ^ i - 2) :
    3 ^ k ∣ 20 * 2 ^ i + i + 1 := BMO5Sol.dvd i b k h
