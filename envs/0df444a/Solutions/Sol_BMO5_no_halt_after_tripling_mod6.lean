-- Prove2me | solution 1 for BMO5.no_halt_after_tripling_mod6
-- status  : ACCEPTED   (prove)
-- author  : @alon yuval
-- created : 2026-11-23T16:42:02.226534+00:00
-- url     : https://prove2.me/submissions/5271a2e6-6222-4154-aa63-a87f0234267e

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

theorem solution (i b k : ℕ) (hk : 1 ≤ k)
    (hi0 : i % 6 ≠ 0) (hi1 : i % 6 ≠ 1) :
    (fun x => 3 * x + i + 5)^[k] b ≠ 10 * 2 ^ i - 2 := by
  intro h
  have h3 : 3 ∣ 20 * 2 ^ i + i + 1 :=
    dvd_trans (by have hp := pow_dvd_pow 3 hk; rwa [pow_one] at hp) (BMO5Sol.dvd i b k h)
  obtain ⟨q, r, hr, rfl⟩ : ∃ q r, r < 2 ∧ i = 2 * q + r :=
    ⟨i / 2, i % 2, Nat.mod_lt _ (by norm_num), (Nat.div_add_mod i 2).symm⟩
  have h4 : 4 ^ q % 3 = 1 := by rw [Nat.pow_mod]; simp
  have e : 2 ^ (2 * q + r) = 4 ^ q * 2 ^ r := by rw [pow_add, pow_mul]; norm_num
  rw [e] at h3
  interval_cases r
  · simp only [pow_zero, mul_one] at h3
    generalize 4 ^ q = Q at h3 h4
    omega
  · simp only [pow_one] at h3
    generalize 4 ^ q = Q at h3 h4
    omega
